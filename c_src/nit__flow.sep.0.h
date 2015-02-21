#include "nit.common.h"
#define COLOR_nit__flow__ToolContext___flow_phase 35
extern const char FILE_nit__flow[];
#define COLOR_nit__phase__Phase___toolcontext 0
extern const char FILE_nit__phase[];
void nit__flow___APropdef___do_flow(val* self, val* p0);
#define COLOR_nit__flow__FlowVisitor___current_flow_context 1
#define COLOR_nit__flow__FlowVisitor___toolcontext 2
#define COLOR_nit__flow___nit__flow__FlowVisitor___standard__kernel__Object__init 50
#define COLOR_nit__flow__FlowVisitor___flows 4
void standard___standard__Array___standard__abstract_collection__SimpleCollection__add(val* self, val* p0);
#define COLOR_nit__flow__FlowContext___is_start 4
#define COLOR_nit__flow__FlowVisitor___first 3
#define COLOR_nit__flow__FlowContext___node 5
#define COLOR_nit__flow__ANode__accept_flow_visitor 43
extern const struct type type_nit__AExpr;
#define COLOR_nit__flow__AExpr___after_flow_context 4
#define COLOR_nit__flow__FlowContext___when_true 7
#define COLOR_standard__kernel__Object___61d_61d 2
#define COLOR_nit__flow__FlowContext___when_false 8
val* nit__flow___nit__flow__FlowVisitor___make_sub_flow(val* self);
val* standard___standard__NativeString___to_s_with_length(char* self, long p0);
#define COLOR_nit__flow__FlowContext___name 6
void nit___nit__Visitor___enter_visit(val* self, val* p0);
val* NEW_nit__FlowContext(const struct type* type);
extern const struct type type_nit__FlowContext;
#define COLOR_nit__parser_nodes__Visitor___current_node 0
void nit___nit__FlowContext___add_previous(val* self, val* p0);
val* nit__flow___nit__flow__FlowVisitor___make_true_false_flow(val* self, val* p0, val* p1);
#define COLOR_nit__flow__FlowContext___is_marked_unreachable 2
#define COLOR_nit__scope__EscapeMark___escapes 2
extern const char FILE_nit__scope[];
val* standard___standard__AbstractArrayRead___standard__abstract_collection__Collection__iterator(val* self);
short int standard__array___standard__array__ArrayIterator___standard__abstract_collection__Iterator__is_ok(val* self);
val* standard__array___standard__array__ArrayIterator___standard__abstract_collection__Iterator__item(val* self);
val* nit__flow___AEscapeExpr___before_flow_context(val* self);
void nit___nit__FlowContext___add_loop(val* self, val* p0);
void standard__array___standard__array__ArrayIterator___standard__abstract_collection__Iterator__next(val* self);
val* nit__flow___nit__flow__FlowVisitor___make_merge_flow(val* self, val* p0, val* p1);
#define COLOR_nit__flow__FlowContext___previous 0
#define COLOR_nit__flow__FlowContext___loops 1
#define COLOR_standard__array__AbstractArrayRead___length 0
#define COLOR_nit__flow__FlowContext___is_already_unreachable 3
short int nit___nit__FlowContext___is_unreachable(val* self);
short int standard___standard__AbstractArrayRead___standard__abstract_collection__Collection__has(val* self, val* p0);
#define COLOR_nit__parser_nodes__ANode__visit_all 40
val* NEW_nit__flow__FlowVisitor(const struct type* type);
extern const struct type type_nit__flow__FlowVisitor;
#define COLOR_nit__flow__FlowVisitor__toolcontext_61d 38
#define COLOR_standard__kernel__Object__init 7
#define COLOR_nit__flow__APropdef___before_flow_context 14
#define COLOR_nit__flow__APropdef___after_flow_context 15
#define COLOR_nit__flow___APropdef___ANode__accept_flow_visitor 94
#define COLOR_nit__flow___AVarAssignExpr___ANode__accept_flow_visitor 92
#define COLOR_nit__flow___AReassignFormExpr___ANode__accept_flow_visitor 95
#define COLOR_nit__parser_nodes__ABlockExpr___n_expr 10
extern const char FILE_nit__parser_nodes[];
val* nit___nit__ANodes___standard__abstract_collection__Collection__iterator(val* self);
#define COLOR_standard__abstract_collection__Iterator__is_ok 34
#define COLOR_standard__abstract_collection__Iterator__item 32
val* nit___nit__ANode___hot_location(val* self);
void nit___nit__ToolContext___error(val* self, val* p0, val* p1);
#define COLOR_standard__abstract_collection__Iterator__next 33
#define COLOR_nit__flow___AReturnExpr___ANode__accept_flow_visitor 83
val* nit__flow___nit__flow__FlowVisitor___make_unreachable_flow(val* self);
val* standard___standard__SequenceRead___Collection__first(val* self);
#define COLOR_nit__flow___AEscapeExpr___ANode__accept_flow_visitor 85
#define COLOR_nit__flow___AAbortExpr___ANode__accept_flow_visitor 81
#define COLOR_nit__flow___ADoExpr___ANode__accept_flow_visitor 88
#define COLOR_nit__scope__ADoExpr___break_mark 13
void nit__flow___nit__flow__FlowVisitor___merge_breaks(val* self, val* p0);
#define COLOR_nit__parser_nodes__AIfExpr___n_expr 11
val* nit__flow___nit__flow__FlowVisitor___visit_expr(val* self, val* p0);
#define COLOR_nit__parser_nodes__AIfExpr___n_then 12
#define COLOR_nit__parser_nodes__AIfExpr___n_else 13
#define COLOR_nit__parser_nodes__AIfexprExpr___n_expr 11
#define COLOR_nit__parser_nodes__AIfexprExpr___n_then 13
#define COLOR_nit__parser_nodes__AIfexprExpr___n_else 15
#define COLOR_nit__parser_nodes__AWhileExpr___n_expr 12
#define COLOR_nit__parser_nodes__AWhileExpr___n_block 14
#define COLOR_nit__scope__AWhileExpr___continue_mark 16
void nit__flow___nit__flow__FlowVisitor___merge_continues_to(val* self, val* p0, val* p1);
#define COLOR_nit__scope__AWhileExpr___break_mark 15
#define COLOR_nit__parser_nodes__ALoopExpr___n_block 12
#define COLOR_nit__scope__ALoopExpr___continue_mark 14
#define COLOR_nit__scope__ALoopExpr___break_mark 13
#define COLOR_nit__parser_nodes__AForExpr___n_expr 13
#define COLOR_nit__parser_nodes__AForExpr___n_block 15
#define COLOR_nit__scope__AForExpr___continue_mark 18
#define COLOR_nit__scope__AForExpr___break_mark 17
#define COLOR_nit__parser_nodes__AAssertExpr___n_expr 12
#define COLOR_nit__parser_nodes__AAssertExpr___n_else 13
#define COLOR_nit__parser_nodes__ABinBoolExpr___n_expr 10
#define COLOR_nit__parser_nodes__ABinBoolExpr___n_expr2 11
#define COLOR_nit__parser_nodes__ANotExpr___n_expr 11
#define COLOR_nit__flow___AOrElseExpr___ANode__accept_flow_visitor 84
#define COLOR_nit__flow___AEqExpr___ANode__accept_flow_visitor 89
val* nit__flow___nit__flow__FlowVisitor___make_sub_true_false_flow(val* self);
#define COLOR_nit__flow___ANeExpr___ANode__accept_flow_visitor 89
#define COLOR_nit__flow___AIsaExpr___ANode__accept_flow_visitor 86
#define COLOR_nit__parser_nodes__AParExpr___n_expr 11
#define COLOR_nit__parser_nodes__AOnceExpr___n_expr 11