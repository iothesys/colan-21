#include "checker.h"
#include "../../aid/map/map.h"
#include "parser.h"

typedef struct Parser_Node pnode_t;
typedef struct Parser_State pstate_t;
typedef struct Token tok_t;
typedef enum Parser_Node_Kind pnode_kind_t;

enum Checker_Subtype {
    SPEC,
    INFERRED_INT,
    INFERRED_FLOAT,
};

struct Checker_Type {
    enum Checker_Subtype subtype;
    struct Parser_Type type;
};  

struct Map OF(pnode_t) env;

static void err(pnode_t *node) {
    eh_error_pos(node->pos, parser_get_state()->lexer.src);
    exit(1);
}

static string annot_str(struct Vec OF(strview_t) *annot) {
    sb_t b = sbstart();
    sbprintf(&b, "\"");
    for (usize i = 0; i < annot->size; i += 1) {
        strview_t *view = vec_get(annot, i);
        sbprintf(&b, "%.*s\n", (int)view->size, view->view);
    }
    sbprintf(&b, "\"");
    return sbend(&b) ? sbend(&b) : strdup("");
}

static pnode_t exec_command(pnode_t *subject, pnode_t *command) {
    pnode_t *arg = vec_get(&command->children, 0);
    if (arg->kind == PN_IDENT) {
        struct Vec annot = subject->data.decl.annotations;
        string comm = annot_str(&annot);
        if (strview_eq(arg->data.ident.val, strview_from("tostring"))) {
            pnode_t node = pnode_endpoint(subject->pos, PN_STRING);
            node.data.string.val = strview_from(comm);
            return node;
        }
        else if (strview_eq(arg->data.ident.val, strview_from("isset"))) {
            pnode_t *arg1 = vec_get(&command->children, 1);
            if (arg1->kind != PN_IDENT) {
                EH_MESSAGE("Use identifier for flag, for example [x | isset flag]");
                err(arg);
            }
            strview_t name = arg1->data.ident.val;
            pnode_t node = pnode_endpoint(subject->pos, PN_NUMBER);
            node.data.number.kind = PNM_INT;
            node.data.number.val = strview_from("0");
            for (usize i = 0; comm[i]; i += 1) {
                if (comm[i] == '^') {
                    i += 1;
                    if (strncmp(name.view, comm+i, name.size) == 0) {
                        node.data.number.val = strview_from("1");
                        return node;
                    }
                }
            }
            return node;
        }
        else {
            EH_MESSAGE("This macro doesn't exist");
            err(arg);
        }
    }
    else {
        EH_MESSAGE("Invalid macro name");
        err(arg);
    }
    exit(1);
}

static void handle_macro(pnode_t *node) {
    if (node->children.size == 0) {
        EH_MESSAGE("Empty macro");
        err(node);
    }
    if (node->children.size != 2) {
        EH_MESSAGE("Too many parameters to macro");
        err(node);
    }
    pnode_t *subject = vec_get(&node->children, 0);
    if (subject->children.size == 0) {
        EH_MESSAGE("Empty subject");
        err(subject);
    }
    subject = vec_get(&subject->children, 0);
    pnode_t *old_subj = subject;
    if (subject->kind != PN_IDENT) {
        EH_MESSAGE("This is not a valid declaration name %d", subject->kind);
        err(subject);
    }
    subject = map_get(&env, subject->data.ident.val);
    if (subject == NULL) {
        EH_MESSAGE("This declaration doesn't exist");
        err(old_subj);
    }
    pnode_t *command = vec_get(&node->children, 1);
    if (command->children.size == 0) {
        EH_MESSAGE("Empty command");
        err(command);
    }
    *node = exec_command(subject, command);
}

void eh_setnote();

static void rec_checker(pnode_t *node, struct Vec OF(strview_t) *decls) {
    switch (node->kind) {
        case PN_MACRO:
            handle_macro(node);
        break;
        case PN_PROC: 
        case PN_BODY:
        case PN_TOPLEVEL:
        case PN_STRUCT: {
            struct Vec OF(strview_t) mydecls = vec_new(sizeof(strview_t));
            for (usize i = 0; i < node->children.size; i += 1) {
                rec_checker(vec_get(&node->children, i), &mydecls);
            }
            for (usize i = 0; i < mydecls.size; i += 1) {
                map_remove(&env, *(strview_t*)vec_get(&mydecls, i));
            }
            vec_drop(&mydecls);
        }
        break;
        case PN_DECL:
            if (map_get(&env, node->data.decl.name) != NULL) {
                pnode_t *previous = map_get(&env, node->data.decl.name);
                EH_MESSAGE("Variable shadowed by following declaration");
                eh_error_pos(previous->pos, parser_get_state()->lexer.src);
                eh_setnote();
                EH_MESSAGE("Shadowed here");
                err(node);
            }   
            map_add(&env, node->data.decl.name, node);
            vec_push(decls, &node->data.decl.name);
            goto def;
        case PN_ASSIGN: {
            pnode_t *lhs = pnode_left(node); 
            if (!(lhs->kind == PN_IDENT || lhs->kind == PN_DECL)) {
                EH_MESSAGE("Can't assign to this");
                err(node);
            }
            if (lhs->kind == PN_IDENT && map_get(&env, lhs->data.ident.val) != NULL) {
                pnode_t *decl = map_get(&env, lhs->data.ident.val);
                if (decl->data.decl.constant) {
                    EH_MESSAGE("Assignment to a constant value");
                    eh_error_pos(node->pos, parser_get_state()->lexer.src);
                    eh_setnote();
                    EH_MESSAGE("Created here");
                    err(decl);   
                }
            }
            else if (lhs->kind == PN_DECL && !lhs->data.decl.constant) {
                pnode_t *rhs = pnode_right(node);
                if (rhs->kind == PN_PROC) {
                    EH_MESSAGE("Direct procedure assignment must be constant. Use `%.*s :: proc ...` instead.", (int)lhs->data.decl.name.size, lhs->data.decl.name.view);
                    err(node);
                }
                if (rhs->kind == PN_STRUCT) {
                    EH_MESSAGE("Struct assignment must be constant. Use `%.*s :: struct ...` instead.", (int)lhs->data.decl.name.size, lhs->data.decl.name.view);
                    err(node);
                }
            }
            goto def;
        }
        def:
        default: 
            for (usize i = 0; i < node->children.size; i += 1) {
                rec_checker(vec_get(&node->children, i), decls);
            }
    }
}

void checker_run(pnode_t *node) {
    env = map_new(sizeof(struct Parser_Node));
    struct Vec decls = vec_new(sizeof(strview_t));
    rec_checker(node, &decls);
    vec_drop(&decls);
}
