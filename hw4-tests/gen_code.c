/* $Id: gen_code.c,v 1.25 2023/11/28 22:12:58 leavens Exp $ */
#include <limits.h>
#include <string.h>
#include "ast.h"
#include "code.h"
#include "id_use.h"
#include "literal_table.h"
#include "gen_code.h"
#include "utilities.h"
#include "code_utils.h"
#include "regname.h"

#define STACK_SPACE 4096

// Initialize the code generator
void gen_code_initialize()
{
    literal_table_initialize();
}

// Requires: bf if open for writing in binary
// and prior to this scope checking and type checking have been done.
// Write all the instructions in cs to bf in order
static void gen_code_output_seq(BOFFILE bf, code_seq cs)
{
    while (!code_seq_is_empty(cs)) {
	bin_instr_t inst = code_seq_first(cs)->instr;
	instruction_write_bin_instr(bf, inst);
	cs = code_seq_rest(cs);
    }
}

// Return a header appropriate for the give code
static BOFHeader gen_code_program_header(BOFFILE bf, code_seq main_cs)
{
    BOFHeader ret;
    bof_write_magic_to_header(&ret);
    ret = bof_read_header(bf);
    return ret;
}

static void gen_code_output_literals(BOFFILE bf)
{
    literal_table_start_iteration();
    while (literal_table_iteration_has_next()) {
        word_type w = literal_table_iteration_next();
        // debug_print("Writing literal %f to BOF file\n", w);
        bof_write_word(bf, w);
    }
    literal_table_end_iteration(); // not necessary
}

// Requires: bf is open for writing in binary
// Write the program's BOFFILE to bf
static void gen_code_output_program(BOFFILE bf, code_seq main_cs)
{
    BOFHeader bfh = gen_code_program_header(bf, main_cs);
    bof_write_header(bf, bfh);
    gen_code_output_seq(bf, main_cs);
    gen_code_output_literals(bf);
    bof_close(bf);
}


// Requires: bf if open for writing in binary
// Generate code for prog into bf
void gen_code_program(BOFFILE bf, block_t prog)
{
    code_seq main_cs;
    // We want to make the main program's AR look like all blocks... so:
    // allocate space and initialize any variables
    main_cs = gen_code_var_decls(prog.var_decls);

    int vars_len_in_bytes = (code_seq_size(main_cs) / 2);
    // there is no static link for the program as a whole,
    // so nothing to do for saving FP into A0 as would be done for a block
    code_seq_concat(&main_cs, code_utils_save_registers_for_AR());
    code_seq_concat(&main_cs, gen_code_stmt());
    code_seq_concat(&main_cs, code_utils_restore_registers_from_AR());
    code_seq_concat(&main_cs, code_utils_deallocate_stack_space(vars_len_in_bytes));
    code_seq_add_to_end(&main_cs, code_exit(exit_sc));
    gen_code_output_program(bf, main_cs);
}

// Generate code for the var_decls_t vds to out
// There are 2 instructions generated for each identifier declared
// (one to allocate space and another to initialize that space)
code_seq gen_code_var_decls(var_decls_t vds)
{
    code_seq ret = code_seq_empty();
    var_decl_t *vdp = vds.var_decls;
    while (vdp != NULL) {
	// generate these in reverse order,
	// so the addressing offsets work properly
        code_seq_concat(&ret, gen_code_var_decl(*vdp));
        vdp = vdp->next;
    }
    return ret;
}

// Generate code for a single <var-decl>, vd,
// There are 2 instructions generated for each identifier declared
// (one to allocate space and another to initialize that space)
code_seq gen_code_var_decl(var_decl_t vd)
{
    return gen_code_idents(vd.ident_list, vd.type_tag);
}

// Generate code for the identififers in idents with type vt
// in reverse order (so the first declared are allocated last).
// There are 2 instructions generated for each identifier declared
// (one to allocate space and another to initialize that space)
code_seq gen_code_idents(ident_list_t idents,
			 AST_type vt)
{
    code_seq ret = code_seq_empty();
    ident_t *idp = idents.start;
    while (idp != NULL) {
    //HY, Fixed this I think.
	code_seq alloc_and_init = code_seq_singleton(code_addi(SP,0,0));
	switch (vt) {
        case block_ast:
            code_seq_add_to_end(&alloc_and_init, code_fsw(SP, 0, 0));
            break;
        case const_decls_ast:
            code_seq_add_to_end(&alloc_and_init, code_fsw(SP, 0, 0));
            break;
        case const_decl_ast:
            code_seq_add_to_end(&alloc_and_init, code_fsw(SP, 0, 0));
            break;
        case const_def_list_ast:
            code_seq_add_to_end(&alloc_and_init, code_fsw(SP, 0, 0));
            break;
        case const_def_ast:
            code_seq_add_to_end(&alloc_and_init, code_fsw(SP, 0, 0));
            break;
        case var_decls_ast:
            code_seq_add_to_end(&alloc_and_init, code_fsw(SP, 0, 0));
            break;
        case var_decl_ast:
            code_seq_add_to_end(&alloc_and_init, code_fsw(SP, 0, 0));
            break;
        case ident_list_ast:
            code_seq_add_to_end(&alloc_and_init, code_fsw(SP, 0, 0));
            break;
        case proc_decls_ast:
            code_seq_add_to_end(&alloc_and_init, code_fsw(SP, 0, 0));
            break;
        case proc_decl_ast:
            code_seq_add_to_end(&alloc_and_init, code_fsw(SP, 0, 0));
            break;
        case stmts_ast:
            code_seq_add_to_end(&alloc_and_init, code_fsw(SP, 0, 0));
            break;
        case empty_ast:
            code_seq_add_to_end(&alloc_and_init, code_fsw(SP, 0, 0));
            break;
        case stmt_list_ast:
            code_seq_add_to_end(&alloc_and_init, code_fsw(SP, 0, 0));
            break;
        case stmt_ast:
            code_seq_add_to_end(&alloc_and_init, code_fsw(SP, 0, 0));
            break;
        case assign_stmt_ast:
            code_seq_add_to_end(&alloc_and_init, code_fsw(SP, 0, 0));
            break;
        case call_stmt_ast:
            code_seq_add_to_end(&alloc_and_init, code_fsw(SP, 0, 0));
            break;
        case if_stmt_ast:
            code_seq_add_to_end(&alloc_and_init, code_fsw(SP, 0, 0));
            break;
        case while_stmt_ast:
            code_seq_add_to_end(&alloc_and_init, code_fsw(SP, 0, 0));
            break;
        case read_stmt_ast:
            code_seq_add_to_end(&alloc_and_init, code_fsw(SP, 0, 0));
            break;
        case print_stmt_ast:
            code_seq_add_to_end(&alloc_and_init, code_fsw(SP, 0, 0));
            break;
        case block_stmt_ast:
            code_seq_add_to_end(&alloc_and_init, code_fsw(SP, 0, 0));
            break;
        case condition_ast:
            code_seq_add_to_end(&alloc_and_init, code_fsw(SP, 0, 0));
            break;
        case db_condition_ast:
            code_seq_add_to_end(&alloc_and_init, code_fsw(SP, 0, 0));
            break;
        case rel_op_condition_ast:
            code_seq_add_to_end(&alloc_and_init, code_fsw(SP, 0, 0));
            break;
        case expr_ast:
            code_seq_add_to_end(&alloc_and_init, code_fsw(SP, 0, 0));
            break;
        case binary_op_expr_ast:
            code_seq_add_to_end(&alloc_and_init, code_fsw(SP, 0, 0));
            break;
        case negated_expr_ast:
            code_seq_add_to_end(&alloc_and_init, code_fsw(SP, 0, 0));
            break;
        case ident_ast:
            code_seq_add_to_end(&alloc_and_init, code_fsw(SP, 0, 0));
            break;
        case number_ast:
            code_seq_add_to_end(&alloc_and_init, code_fsw(SP, 0, 0));
            break;
        case token_ast:
            code_seq_add_to_end(&alloc_and_init, code_fsw(SP, 0, 0));
            break;
        
        default:
            bail_with_error("Bad AST_type (%d) passed to gen_code_idents!",
                    vt);
            break;
	}
	// Generate these in revese order,
	// so addressing works propertly
	code_seq_concat(&alloc_and_init, ret);
	idp = idp->next;
    }
    return ret;
}

// Generate code for stmt
code_seq gen_code_stmt(stmt_t stmt)
{
    //HY Impliment call while print block
    switch (stmt.stmt_kind) {
    case assign_stmt:
        return gen_code_assign_stmt(stmt.data.assign_stmt);
        break;
    case call_stmt:
        return gen_code_call_stmt(stmt.data.call_stmt);
        break;
    case if_stmt:
        return gen_code_if_stmt(stmt.data.if_stmt);
        break;
    case while_stmt:
        return gen_code_while_stmt(stmt.data.while_stmt);
        break;
    case read_stmt:
        return gen_code_read_stmt(stmt.data.read_stmt);
        break;
    case print_stmt:
        return gen_code_print_stmt(stmt.data.print_stmt);
        break;
    case block_stmt:
        return gen_code_block_stmt(stmt.data.block_stmt);
        break;
    default:
        bail_with_error("Call to gen_code_stmt with an AST that is not a statement!");
        break;
    }
    // The following can never execute, but this quiets gcc's warning
    return code_seq_empty();
}

// Generate code for stmt
code_seq gen_code_assign_stmt(assign_stmt_t stmt)
{
    // can't call gen_code_ident,
    // since stmt.name is not an ident_t
    code_seq ret;
    // put value of expression in $v0
    ret = gen_code_expr(*(stmt.expr));
    assert(stmt.idu != NULL);
    assert(id_use_get_attrs(stmt.idu) != NULL);
    AST_type typ = id_use_get_attrs(stmt.type_tag)->kind;
    code_seq_concat(&ret, code_pop_stack_into_reg(V0, typ));
    // put frame pointer from the lexical address of the name
    // (using stmt.idu) into $t9
    ret = code_seq_concat(&ret, code_compute_fp(T9, stmt.idu->levelsOutward));
    unsigned int offset_count = id_use_get_attrs(stmt.idu)->offset_count;
    assert(offset_count <= USHRT_MAX); // it has to fit!
    switch (id_use_get_attrs(stmt.idu->levelsOutward)) {
    case float_te:
	ret = code_seq_add_to_end(ret,
				  code_fsw(T9, V0, offset_count));
	break;
    case bool_te:
	ret = code_seq_add_to_end(ret,
				  code_sw(T9, V0, offset_count));
	break;
    default:
	bail_with_error("Bad var_type (%d) for ident in assignment stmt!",
			id_use_get_attrs(stmt.idu)->type);
	break;
    }
    return ret;
}
code_seq gen_code_call_stmt(call_stmt_t stmts){

}


/* Generate code for stmt
code_seq gen_code_begin_stmt(begin_stmt_t stmt)
{
    code_seq ret;
    // allocate space and initialize any variables in block
    ret = gen_code_var_decls(stmt.var_decls);
    int vars_len_in_bytes = (code_seq_size(ret) / 2)
    // in FLOAT, surrounding scope's base is FP, so that is the static link
    ret = code_seq_add_to_end(ret, code_add(0, FP, A0));
    ret = code_seq_concat(ret, code_save_registers_for_AR());
    ret = code_seq_concat(ret, gen_code_stmts(stmt.stmts));
    ret = code_seq_concat(ret, code_restore_registers_from_AR());
    ret = code_seq_concat(ret, code_deallocate_stack_space(vars_len_in_bytes));
    return ret;
}
*/

// Generate code for the list of statments given by stmts
code_seq gen_code_stmts(stmts_t stmts)
{
    code_seq ret = code_seq_empty();
    stmt_t *sp = stmts.stmt_list.start;
    while (sp != NULL) {
        code_seq_concat(&ret, gen_code_stmt(*sp));
        sp = sp->next;
    }
    return ret;
}

// Generate code for the if-statment given by stmt
code_seq gen_code_if_stmt(if_stmt_t stmt)
{
    // put truth value of stmt.expr in $v0
    code_seq ret = gen_code_expr(stmt.condition);
    ret = code_seq_concat(ret, code_pop_stack_into_reg(V0, bool_te));
    code_seq cbody = gen_code_stmt(*(stmt.body));
    int cbody_len = code_seq_size(cbody);
    // skip over body if $v0 contains false
    ret = code_seq_add_to_end(ret,
			      code_beq(V0, 0, cbody_len));
    return code_seq_concat(ret, cbody);
}
code_seq gen_code_while_stmt(while_stmt_t stmts){

}

// Generate code for the read statment given by stmt
code_seq gen_code_read_stmt(read_stmt_t stmt)
{
    // put number read into $v0
    code_seq ret = code_seq_singleton(code_rch());
    // put frame pointer from the lexical address of the name
    // (using stmt.idu) into $t9
    assert(stmt.idu != NULL);
    ret = code_seq_concat(ret,
			  code_compute_fp(T9, stmt.idu->levelsOutward));
    assert(id_use_get_attrs(stmt.idu) != NULL);
    unsigned int offset_count = id_use_get_attrs(stmt.idu)->offset_count;
    assert(offset_count <= USHRT_MAX); // it has to fit!
    ret = code_seq_add_to_end(ret,
			      code_seq_singleton(code_fsw(T9, V0, offset_count)));
    return ret;
}
code_seq gen_code_print_stmt(print_stmt_t stmts){

}
code_seq gen_code_block_stmt(block_stmt_t stmts){

}

/* Generate code for the write statment given by stmt.
code_seq gen_code_write_stmt(write_stmt_t stmt)
{
    // put the result into $a0 to get ready for PCH
    code_seq ret
	= gen_code_expr(stmt.expr);
    ret = code_seq_concat(ret, code_pop_stack_into_reg(A0, float_te));
    ret = code_seq_add_to_end(ret, code_pflt());
    return ret;
}
*/
// Generate code for the expression exp
// putting the result on top of the stack,
// and using V0 and AT as temporary registers
// May also modify SP, HI,LO when executed
code_seq gen_code_expr(expr_t exp)
{
    switch (exp.expr_kind) {
    case expr_bin:
	return gen_code_binary_op_expr(exp.data.binary);
	break;
    case expr_ident:
	return gen_code_ident(exp.data.ident);
	break;
    case expr_number:
	return gen_code_number(exp.data.number);
	break;
    case expr_negated:
    //HY I think I fixed this.
	return gen_code_logical_not_expr(exp);
	break;
    default:
	bail_with_error("Unexpected expr_kind_e (%d) in gen_code_expr",
			exp.expr_kind);
	break;
    }
    // never happens, but suppresses a warning from gcc
    return code_seq_empty();
}

// Generate code for the expression exp
// putting the result on top of the stack,
// and using V0 and AT as temporary registers
// May also modify SP, HI,LO when executed
code_seq gen_code_binary_op_expr(binary_op_expr_t exp)
{
    // put the values of the two subexpressions on the stack
    code_seq ret = gen_code_expr(*(exp.expr1));
     ret = code_seq_concat(&ret, gen_code_expr(*(exp.expr2)));
    // check the types match
    AST_type t1 = ast_expr_type(*(exp.expr1));
    assert(ast_expr_type(*(exp.expr2)) == t1);
    // do the operation, putting the result on the stack
    ret = code_seq_concat(&ret, gen_code_op(exp.arith_op, t1));
    return ret;
}

// Generate code to apply op to the
// 2nd from top and top of the stack,
// putting the result on top of the stack in their place,
// and using V0 and AT as temporary registers
// Modifies SP when executed
code_seq gen_code_op(token_t op, AST_type typ)
{
    switch (op.code) {
    case eqsym: case neqsym:
    case ltsym: case leqsym:
    case gtsym: case geqsym:
	return gen_code_rel_op(op, typ);
	break;
    case plussym: case minussym: case multsym: case divsym:
	assert(typ == float_te);
	return gen_code_arith_op(op);
	break;
    default:
	bail_with_error("Unknown token code (%d) in gen_code_op",
			op.code);
	break;
    }
    return code_seq_empty();
}

// Generate code to apply the floating-point arith_op to the
// 2nd from top and top of the stack,
// putting the result on top of the stack in their place,
// and using V0 and AT as temporary registers
// Also modifies SP when executed
code_seq gen_code_arith_op(token_t arith_op)
{
    // load top of the stack (the second operand) into AT
    code_seq ret = code_pop_stack_into_reg(AT, float_te);
    // load next element of the stack into V0
    ret = code_seq_concat(ret, code_pop_stack_into_reg(V0, float_te));

    code_seq do_op = code_seq_empty();
    switch (arith_op.code) {
    case plussym:
	do_op = code_seq_add_to_end(do_op, code_fadd(V0, AT, V0));
	break;
    case minussym:
	do_op = code_seq_add_to_end(do_op, code_fsub(V0, AT, V0));
	break;
    case multsym:
	do_op = code_seq_add_to_end(do_op, code_fmul(V0, AT, V0));
	break;
    case divsym:
	do_op = code_seq_add_to_end(do_op, code_fdiv(V0, AT, V0));
	break;
    default:
	bail_with_error("Unexpected arithOp (%d) in gen_code_arith_op",
			arith_op.code);
	break;
    }
    do_op = code_seq_concat(do_op, code_push_reg_on_stack(V0, float_te));
    return code_seq_concat(ret, do_op);
}

// Generate code for the rel_op
// applied to 2nd from top and top of the stack,
// putting the result on top of the stack in their place,
// and using V0 and AT as temporary registers
// Also modifies SP when executed
code_seq gen_code_rel_op(token_t rel_op, AST_type typ)
{
    // load top of the stack (the second operand) into AT
    code_seq ret = code_pop_stack_into_reg(AT, typ);
    // load next element of the stack into V0
    ret = code_seq_concat(ret, code_pop_stack_into_reg(V0, typ));

    // start out by doing the comparison
    // and skipping the next 2 instructions if it's true
    code_seq do_op = code_seq_empty();
    switch (rel_op.code) {
    case eqsym: 
	if (typ == float_te) {
	    do_op = code_seq_singleton(code_bfeq(V0, AT, 2));
	} else {
	    do_op = code_seq_singleton(code_beq(V0, AT, 2));
	}
	break;
    case neqsym:
	if (typ == float_te) {
	    do_op = code_seq_singleton(code_bfne(V0, AT, 2));
	} else {
	    do_op = code_seq_singleton(code_bne(V0, AT, 2));
	}
	break;
    case ltsym:
	if (typ == float_te) {
	    do_op = code_seq_singleton(code_fsub(V0, AT, V0));
	    do_op = code_seq_add_to_end(do_op, code_bfltz(V0, 2));
	} else {
	    do_op = code_seq_singleton(code_sub(V0, AT, V0));
	    do_op = code_seq_add_to_end(do_op, code_bltz(V0, 2));
	}
	break;
    case leqsym:
	if (typ == float_te) {
	    do_op = code_seq_singleton(code_fsub(V0, AT, V0));
	    do_op = code_seq_add_to_end(do_op, code_bflez(V0, 2));
	} else {
	    do_op = code_seq_singleton(code_sub(V0, AT, V0));
	    do_op = code_seq_add_to_end(do_op, code_blez(V0, 2));
	}
	break;
    case gtsym:
	if (typ == float_te) {
	    do_op = code_seq_singleton(code_fsub(V0, AT, V0));
	    do_op = code_seq_add_to_end(do_op, code_bfgtz(V0, 2));
	} else {
	    do_op = code_seq_singleton(code_sub(V0, AT, V0));
	    do_op = code_seq_add_to_end(do_op, code_bgtz(V0, 2));
	}
	break;
    case geqsym:
	if (typ == float_te) {
	    do_op = code_seq_singleton(code_fsub(V0, AT, V0));
	    do_op = code_seq_add_to_end(do_op, code_bfgez(V0, 2));
	} else {
	    do_op = code_seq_singleton(code_sub(V0, AT, V0));
	    do_op = code_seq_add_to_end(do_op, code_bgez(V0, 2));
	}
	break;
    default:
	bail_with_error("Unknown token code (%d) in gen_code_rel_op",
			rel_op.code);
	break;
    }
    ret = code_seq_concat(ret, do_op);
    // rest of the code for the comparisons
    ret = code_seq_add_to_end(ret, code_add(0, 0, AT)); // put false in AT
    ret = code_seq_add_to_end(ret, code_beq(0, 0, 1)); // skip next instr
    ret = code_seq_add_to_end(ret, code_addi(0, AT, 1)); // put true in AT
    ret = code_seq_concat(ret, code_push_reg_on_stack(AT, bool_te));
    return ret;
}

// Generate code to put the value of the given identifier
// on top of the stack
// Modifies T9, V0, and SP when executed
code_seq gen_code_ident(ident_t id)
{
    assert(id.idu != NULL);
    code_seq ret = code_compute_fp(T9, id.idu->levelsOutward);
    assert(id_use_get_attrs(id.idu) != NULL);
    unsigned int offset_count = id_use_get_attrs(id.idu)->offset_count;
    assert(offset_count <= USHRT_MAX); // it has to fit!
    AST_type typ = id_use_get_attrs(id.idu)->type;
    if (typ == float_te) {
	ret = code_seq_add_to_end(ret,
				  code_flw(T9, V0, offset_count));
    } else {
	ret = code_seq_add_to_end(ret,
				  code_lw(T9, V0, offset_count));
    }
    return code_seq_concat(ret, code_push_reg_on_stack(V0, typ));
}

// Generate code to put the given number on top of the stack
// Modifies V0 when executed
code_seq gen_code_number(number_t num)
{
    unsigned int global_offset
	= literal_table_lookup(num.text, num.value);
    return code_seq_concat(code_seq_singleton(code_flw(GP, V0, global_offset)),
			   code_push_reg_on_stack(V0, float_te));
}

// Generate code for the expression exp
// putting the result on top of the stack,
// and using V0 and AT as temporary registers
// May also modify SP, HI,LO when executed
code_seq gen_code_logical_not_expr(expr_t exp)
{
    code_seq ret = gen_code_expr(exp);
    ret = code_seq_concat(ret, code_pop_stack_into_reg(AT, bool_te));
    // if 0 skip next 2 instructions
    ret = code_seq_add_to_end(ret, code_beq(0, AT, 2));
    // it was 1, so put 0 in AT
    ret = code_seq_add_to_end(ret, code_add(0, 0, AT));
    // and skip the next instruction
    ret = code_seq_add_to_end(ret, code_beq(0, 0, 1));
    // put 1 in AT
    ret = code_seq_add_to_end(ret, code_addi(0, AT, 1));
    // push the result on the stack
    ret = code_seq_concat(ret, code_push_reg_on_stack(AT, bool_te));
    return ret;
}