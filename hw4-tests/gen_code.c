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

/* === Initialization === */

/**
 * Initialize the code generator.
 * This function sets up the literal table for managing constants.
 */
void gen_code_initialize() {
    literal_table_initialize();  // Initialize the literal table.
}

/* === Helper Functions === */

/**
 * Writes all instructions in a code sequence (`cs`) to the binary object file (`bf`).
 * 
 * @param bf - The binary object file, open for writing.
 * @param cs - The sequence of instructions to write.
 */
static void gen_code_output_seq(BOFFILE bf, code_seq cs) {
    while (!code_seq_is_empty(cs)) {
        // Write the binary instruction to the BOF file.
        bin_instr_t inst = code_seq_first(cs)->instr;
        instruction_write_bin_instr(bf, inst);
        cs = code_seq_rest(cs);
    }
}


/**
 * Generates and returns a program header for the BOF file.
 * 
 * @param bf - The binary object file.
 * @param main_cs - The main code sequence for the program.
 * @return BOFHeader - A fully initialized header for the program.
 */
static BOFHeader gen_code_program_header(BOFFILE bf, code_seq main_cs) {
    BOFHeader header;
    bof_write_magic_to_header(&header);
    return bof_read_header(bf);
}


/**
 * Outputs all literals stored in the literal table to the BOF file.
 * 
 * @param bf - The binary object file, open for writing.
 */
static void gen_code_output_literals(BOFFILE bf) {
    literal_table_start_iteration();
    while (literal_table_iteration_has_next()) {
        word_type literal = literal_table_iteration_next();
        bof_write_word(bf, literal);  // Write each literal to the BOF file.
    }
    literal_table_end_iteration();  // End iteration (not strictly necessary).
}

/**
 * Writes the full program, including its instructions and literals, to the BOF file.
 * 
 * @param bf - The binary object file, open for writing.
 * @param main_cs - The main code sequence to output.
 */
static void gen_code_output_program(BOFFILE bf, code_seq main_cs) {
    BOFHeader header = gen_code_program_header(bf, main_cs);
    bof_write_header(bf, header);  // Write the program header.
    gen_code_output_seq(bf, main_cs);  // Write the main instructions.
    gen_code_output_literals(bf);  // Write the literals from the table.
    bof_close(bf);  // Close the binary object file.
}


/* === Main Code Generation === */

/**
 * Generates machine code for the program and writes it to the BOF file.
 *
 * @param bf - The binary object file, open for writing.
 * @param prog - The program's abstract syntax tree (AST).
 */
void gen_code_program(BOFFILE bf, block_t prog) {
    code_seq main_cs = gen_code_var_decls(prog.var_decls);  // Process variable declarations.

    int vars_len_in_bytes = code_seq_size(main_cs) / 2;  // Calculate space for variables.

    // Add activation record setup and main block code.
    code_seq_concat(&main_cs, code_utils_save_registers_for_AR());
    code_seq_concat(&main_cs, gen_code_stmt(prog.stmts));  // Main block statements.
    code_seq_concat(&main_cs, code_utils_restore_registers_from_AR());
    code_seq_concat(&main_cs, code_utils_deallocate_stack_space(vars_len_in_bytes));
    code_seq_add_to_end(&main_cs, code_exit(exit_sc));  // Add exit instruction.

    // Write the program to the binary file.
    gen_code_output_program(bf, main_cs);
}

/* === Variable Declarations === */

/**
 * Generate code for variable declarations.
 * Each variable requires two instructions: one to allocate space
 * and one to initialize it.
 *
 * @param vds - The variable declarations AST node.
 * @return code_seq - A sequence of instructions for the declarations.
 */
code_seq gen_code_var_decls(var_decls_t vds) {
    code_seq ret = code_seq_empty();
    var_decl_t *vdp = vds.var_decls;

    while (vdp != NULL) {
        code_seq_concat(&ret, gen_code_var_decl(*vdp));  // Generate code for each variable declaration.
        vdp = vdp->next;
    }
    return ret;
}

/**
 * Generate code for a single variable declaration.
 *
 * @param vd - The single variable declaration AST node.
 * @return code_seq - A sequence of instructions for the variable.
 */
code_seq gen_code_var_decl(var_decl_t vd) {
    return gen_code_idents(vd.ident_list, vd.type_tag);  // Generate code for identifiers.
}

/**
 * Generate code for identifiers in the list with type `vt`.
 *
 * Each identifier generates two instructions:
 * - One to allocate space on the stack.
 * - Another to initialize the space (0 for variables, constant values for constants).
 *
 * @param idents - The list of identifiers to generate code for.
 * @param vt - The type of the identifiers (AST_type).
 * @return code_seq - The sequence of instructions for the identifiers.
 */
code_seq gen_code_idents(ident_list_t idents, AST_type vt) {
    code_seq ret = code_seq_empty();  // Final code sequence.
    ident_t *idp = idents.start;      // Pointer to the first identifier.

    while (idp != NULL) {
        // Allocate space for the identifier.
        code_seq alloc_and_init = code_seq_singleton(code_addi(SP, SP, -1));

        switch (vt) {
            case const_decls_ast:
                // Load constant value into register V0 and store it on the stack.
                alloc_and_init = code_seq_concat(alloc_and_init, code_li(V0, idp->value));
                alloc_and_init = code_seq_add_to_end(alloc_and_init, code_sw(SP, 0, V0));
                break;

            case var_decls_ast:
                // Initialize variable with 0.
                alloc_and_init = code_seq_add_to_end(alloc_and_init, code_sw(SP, 0, 0));
                break;

            default:
                bail_with_error("Unsupported AST_type (%d) in gen_code_idents!", vt);
                break;
        }

        ret = code_seq_concat(alloc_and_init, ret);  // Append the generated code.
        idp = idp->next;  // Move to the next identifier.
    }

    return ret;
}


/**
 * Generate code for a given statement.
 *
 * Dispatches to the appropriate function based on the statement type.
 *
 * @param stmt - The statement to generate code for.
 * @return code_seq - The generated code sequence.
 */
code_seq gen_code_stmt(stmt_t stmt) {
    switch (stmt.stmt_kind) {
        case assign_stmt:
            return gen_code_assign_stmt(stmt.data.assign_stmt);
        case call_stmt:
            return gen_code_call_stmt(stmt.data.call_stmt);
        case if_stmt:
            return gen_code_if_stmt(stmt.data.if_stmt);
        case while_stmt:
            return gen_code_while_stmt(stmt.data.while_stmt);
        case read_stmt:
            return gen_code_read_stmt(stmt.data.read_stmt);
        case print_stmt:
            return gen_code_print_stmt(stmt.data.print_stmt);
        case block_stmt:
            return gen_code_block_stmt(stmt.data.block_stmt);
        default:
            bail_with_error("Invalid statement type in gen_code_stmt!");
    }
    return code_seq_empty();  // Unreachable, but added for safety.
}


/**
 * Generate code for an assignment statement.
 *
 * The expression is evaluated and stored in the corresponding variable.
 *
 * @param stmt - The assignment statement.
 * @return code_seq - The generated code sequence.
 */
code_seq gen_code_assign_stmt(assign_stmt_t stmt) {
    code_seq ret = gen_code_expr(*(stmt.expr));  // Evaluate the expression.

    assert(stmt.idu != NULL);
    assert(id_use_get_attrs(stmt.idu) != NULL);

    AST_type typ = id_use_get_attrs(stmt.idu)->type;
    ret = code_seq_concat(ret, code_util_stack_into_reg(V0, typ));  // Store result in V0.

    ret = code_seq_concat(ret, code_compute_fp(T9, stmt.idu->levelsOutward));  // Compute frame pointer.
    unsigned int offset_count = id_use_get_attrs(stmt.idu)->offset_count;
    assert(offset_count <= USHRT_MAX);

    // Store the result in the variable's memory location.
    switch (typ) {
        case float_te:
            ret = code_seq_add_to_end(ret, code_fsw(T9, V0, offset_count));
            break;
        case bool_te:
            ret = code_seq_add_to_end(ret, code_sw(T9, V0, offset_count));
            break;
        default:
            bail_with_error("Unsupported variable type in gen_code_assign_stmt!");
    }
    return ret;
}


/**
 * Generate code for a procedure call statement.
 *
 * @param stmt - The call statement AST node.
 * @return code_seq - The generated code sequence.
 */
code_seq gen_code_call_stmt(call_stmt_t stmt) {
    code_seq ret = code_seq_empty();

    // Generate code for evaluating arguments in reverse order
    expr_t *arg = stmt.arguments;
    while (arg != NULL) {
        code_seq arg_code = gen_code_expr(*arg);
        ret = code_seq_concat(ret, arg_code);
        arg = arg->next;
    }

    // Generate call instruction
    ret = code_seq_add_to_end(ret, code_call(stmt.proc_name));
    return ret;
}

/**
 * Generate code for a while statement.
 *
 * @param stmt - The while statement AST node.
 * @return code_seq - The generated code sequence.
 */
code_seq gen_code_while_stmt(while_stmt_t stmt) {
    code_seq condition = gen_code_expr(stmt.condition);  // Evaluate the condition.
    code_seq body = gen_code_stmt(stmt.body);            // Generate body code.

    int condition_len = code_seq_size(condition);
    int body_len = code_seq_size(body);

    code_seq ret = code_seq_empty();
    ret = code_seq_concat(ret, condition);
    ret = code_seq_add_to_end(ret, code_beq(V0, 0, body_len + 1));  // Exit if condition is false.
    ret = code_seq_concat(ret, body);
    ret = code_seq_add_to_end(ret, code_bnez(V0, -(condition_len + body_len + 2)));  // Repeat loop.

    return ret;
}


/**
 * Generate code for a print statement.
 *
 * @param stmt - The print statement AST node.
 * @return code_seq - The generated code sequence.
 */
code_seq gen_code_print_stmt(print_stmt_t stmt) {
    code_seq ret = gen_code_expr(stmt.expr);  // Evaluate the expression to print.
    ret = code_seq_concat(ret, code_pop_stack_into_reg(A0, float_te));  // Load result into $a0.
    ret = code_seq_add_to_end(ret, code_print_float());  // Call print routine.
    return ret;
}


/**
 * Generate code for a block statement.
 *
 * Allocates space for variables, generates code for the block's statements,
 * and cleans up the stack upon exiting the block.
 *
 * @param stmt - The block statement.
 * @return code_seq - The generated code sequence.
 */
code_seq gen_code_block_stmt(block_stmt_t stmt) {
    code_seq ret = gen_code_var_decls(stmt.var_decls); // Allocate space for variables.
    int vars_len_in_bytes = code_seq_size(ret) / 2;

    // Setup AR and process block statements.
    ret = code_seq_add_to_end(ret, code_add(FP, A0, 0));
    ret = code_seq_concat(ret, code_utils_save_registers_for_AR());
    ret = code_seq_concat(ret, gen_code_stmts(stmt.stmts));
    ret = code_seq_concat(ret, code_utils_restore_registers_from_AR());
    ret = code_seq_concat(ret, code_utils_deallocate_stack_space(vars_len_in_bytes));
    return ret;
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

/**
 * Generate code for a list of statements.
 *
 * Processes each statement in the list and concatenates the generated code.
 *
 * @param stmts - The list of statements.
 * @return code_seq - The generated code sequence.
 */
code_seq gen_code_stmts(stmts_t stmts) {
    code_seq ret = code_seq_empty();
    stmt_t *sp = stmts.stmts;
    while (sp != NULL) {
        ret = code_seq_concat(ret, gen_code_stmt(*sp));
        sp = sp->next;
    }
    return ret;
}

/**
 * Generate code for an if statement.
 *
 * Evaluates the condition and executes the body if the condition is true.
 *
 * @param stmt - The if statement.
 * @return code_seq - The generated code sequence.
 */
code_seq gen_code_if_stmt(if_stmt_t stmt) {
    code_seq ret = gen_code_expr(stmt.expr); // Generate code for the condition.
    ret = code_seq_concat(ret, code_pop_stack_into_reg(V0, bool_te));

    code_seq cbody = gen_code_stmt(*(stmt.body));
    int cbody_len = code_seq_size(cbody);

    // Skip body execution if condition is false.
    ret = code_seq_add_to_end(ret, code_beq(V0, 0, cbody_len));
    return code_seq_concat(ret, cbody);
}

/**
 * Generate code for a read statement.
 *
 * Reads a value into the specified variable.
 *
 * @param stmt - The read statement.
 * @return code_seq - The generated code sequence.
 */
code_seq gen_code_read_stmt(read_stmt_t stmt) {
    code_seq ret = code_seq_singleton(code_rch()); // Read character into V0.
    
    assert(stmt.idu != NULL);
    ret = code_seq_concat(ret, code_compute_fp(T9, stmt.idu->levelsOutward));

    assert(id_use_get_attrs(stmt.idu) != NULL);
    unsigned int offset_count = id_use_get_attrs(stmt.idu)->offset_count;
    assert(offset_count <= USHRT_MAX);

    ret = code_seq_add_to_end(ret, code_fsw(T9, V0, offset_count));
    return ret;
}

/**
 * Generate code for an expression.
 * The result is placed on top of the stack.
 *
 * @param exp - The expression to evaluate.
 * @return code_seq - The generated code sequence.
 */
code_seq gen_code_expr(expr_t exp) {
    switch (exp.expr_kind) {
        case expr_bin_op:
            return gen_code_binary_op_expr(exp.data.binary);
        case expr_ident:
            return gen_code_ident(exp.data.ident);
        case expr_number:
            return gen_code_number(exp.data.number);
        case expr_logical_not:
            return gen_code_logical_not_expr(*(exp.data.logical_not));
        default:
            bail_with_error("Invalid expression type in gen_code_expr!");
    }
    return code_seq_empty();  // Unreachable, but added for safety.
}


// Generate code for the expression exp
// putting the result on top of the stack,
// and using V0 and AT as temporary registers
// May also modify SP, HI,LO when executed
code_seq gen_code_binary_op_expr(binary_op_expr_t exp)
{
    // put the values of the two subexpressions on the stack
    code_seq ret = gen_code_expr(*(exp.expr1));
    ret = code_seq_concat(ret, gen_code_expr(*(exp.expr2)));
    // check the types match
    AST_type t1 = ast_expr_type(*(exp.expr1));
    assert(ast_expr_type(*(exp.expr2)) == t1);
    // do the operation, putting the result on the stack
    ret = code_seq_concat(ret, gen_code_op(exp.op, t1));
    return ret;
}

/**
 * Generate code for relational comparisons.
 *
 * Compares the top two elements of the stack and pushes the result (true/false) back.
 *
 * @param rel_op - The relational operator token (e.g., <, >, ==).
 * @param typ - The type of the operands.
 * @return code_seq - The generated code sequence.
 */
code_seq gen_code_rel_op(token_t rel_op, AST_type typ) {
    code_seq ret = code_pop_stack_into_reg(AT, typ);  // Load second operand into AT.
    ret = code_seq_concat(ret, code_pop_stack_into_reg(V0, typ));  // Load first operand into V0.

    code_seq do_op = code_seq_empty();
    switch (rel_op.code) {
        case eqsym:
            do_op = code_seq_singleton((typ == float_te) ? code_bfeq(V0, AT, 2) : code_beq(V0, AT, 2));
            break;
        case neqsym:
            do_op = code_seq_singleton((typ == float_te) ? code_bfne(V0, AT, 2) : code_bne(V0, AT, 2));
            break;
        default:
            bail_with_error("Unknown relational operator in gen_code_rel_op!");
    }

    // Add instructions for setting true/false on the stack.
    ret = code_seq_concat(ret, do_op);
    ret = code_seq_add_to_end(ret, code_add(0, 0, AT));  // Set false.
    ret = code_seq_add_to_end(ret, code_beq(0, 0, 1));   // Skip next instruction.
    ret = code_seq_add_to_end(ret, code_addi(0, AT, 1)); // Set true.
    return code_seq_concat(ret, code_push_reg_on_stack(AT, bool_te));
}

/* === Arithmetic Operations === */

/**
 * Generate code for floating-point arithmetic operations.
 * 
 * Applies the arithmetic operation (`arith_op`) to the top two elements of the stack.
 * The result replaces these two elements, with the result pushed back on the stack.
 * Uses V0 and AT as temporary registers and modifies SP during execution.
 * 
 * @param arith_op - The token representing the arithmetic operation (+, -, *, /).
 * @return code_seq - The sequence of instructions for the operation.
 */
code_seq gen_code_arith_op(token_t arith_op) {
    // Pop the top of the stack (second operand) into AT.
    code_seq ret = code_pop_stack_into_reg(AT, float_te);

    // Pop the next element of the stack (first operand) into V0.
    ret = code_seq_concat(ret, code_pop_stack_into_reg(V0, float_te));

    // Perform the specified arithmetic operation.
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
            bail_with_error("Unexpected arith_op (%d) in gen_code_arith_op", arith_op.code);
    }

    // Push the result back onto the stack.
    do_op = code_seq_concat(do_op, code_push_reg_on_stack(V0, float_te));

    // Return the complete sequence.
    return code_seq_concat(ret, do_op);
}


/* === Relational Operations === */

/**
 * Generate code for relational comparisons.
 * 
 * Compares the top two elements of the stack based on the given relational operator (`rel_op`).
 * The result is pushed back on the stack as a boolean value.
 * Uses V0 and AT as temporary registers and modifies SP during execution.
 * 
 * @param rel_op - The token representing the relational operator (==, !=, <, <=, >, >=).
 * @param typ - The type of the operands (e.g., float or integer).
 * @return code_seq - The sequence of instructions for the comparison.
 */
code_seq gen_code_rel_op(token_t rel_op, AST_type typ) {
    // Pop the top of the stack (second operand) into AT.
    code_seq ret = code_pop_stack_into_reg(AT, typ);

    // Pop the next element of the stack (first operand) into V0.
    ret = code_seq_concat(ret, code_pop_stack_into_reg(V0, typ));

    // Generate code for the relational comparison.
    code_seq do_op = code_seq_empty();
    switch (rel_op.code) {
        case eqsym:
            do_op = code_seq_singleton((typ == float_te) ? code_bfeq(V0, AT, 2) : code_beq(V0, AT, 2));
            break;
        case neqsym:
            do_op = code_seq_singleton((typ == float_te) ? code_bfne(V0, AT, 2) : code_bne(V0, AT, 2));
            break;
        case ltsym:
        case leqsym:
        case gtsym:
        case geqsym:
            // Handle floating-point and integer-specific comparisons.
            do_op = code_seq_singleton((typ == float_te) ? code_fsub(V0, AT, V0) : code_sub(V0, AT, V0));
            do_op = code_seq_add_to_end(do_op, (typ == float_te) ? code_bfltz(V0, 2) : code_bltz(V0, 2));
            break;
        default:
            bail_with_error("Unknown rel_op (%d) in gen_code_rel_op", rel_op.code);
    }

    // Add instructions to handle boolean results (true/false).
    ret = code_seq_concat(ret, do_op);
    ret = code_seq_add_to_end(ret, code_add(0, 0, AT));  // Put false in AT.
    ret = code_seq_add_to_end(ret, code_beq(0, 0, 1));   // Skip next instruction if false.
    ret = code_seq_add_to_end(ret, code_addi(0, AT, 1)); // Put true in AT.
    ret = code_seq_concat(ret, code_push_reg_on_stack(AT, bool_te));

    return ret;
}

/* === Identifiers === */

/**
 * Generate code to load the value of an identifier onto the stack.
 * 
 * Uses T9 and V0 as temporary registers and modifies SP during execution.
 * 
 * @param id - The identifier whose value is to be loaded.
 * @return code_seq - The sequence of instructions to load the identifier's value.
 */
code_seq gen_code_ident(ident_t id) {
    assert(id.idu != NULL);
    code_seq ret = code_compute_fp(T9, id.idu->levelsOutward);

    assert(id_use_get_attrs(id.idu) != NULL);
    unsigned int offset_count = id_use_get_attrs(id.idu)->offset_count;
    assert(offset_count <= USHRT_MAX); // Ensure the offset fits.

    AST_type typ = id_use_get_attrs(id.idu)->type;
    if (typ == float_te) {
        ret = code_seq_add_to_end(ret, code_flw(T9, V0, offset_count));
    } else {
        ret = code_seq_add_to_end(ret, code_lw(T9, V0, offset_count));
    }

    // Push the loaded value onto the stack.
    return code_seq_concat(ret, code_push_reg_on_stack(V0, typ));
}


/* === Numbers === */

/**
 * Generate code to load a numeric constant onto the stack.
 *
 * @param num - The numeric constant.
 * @return code_seq - The generated code sequence.
 */
code_seq gen_code_number(number_t num) {
    unsigned int global_offset = literal_table_lookup(num.text, num.value);
    return code_seq_concat(
        code_seq_singleton(code_flw(GP, V0, global_offset)),  // Load number.
        code_push_reg_on_stack(V0, float_te)                 // Push onto stack.
    );
}


/* === Logical NOT === */

/**
 * Generate code for a logical NOT operation on a boolean expression.
 * 
 * Puts the result (true/false) back on the stack.
 * Uses AT as a temporary register and modifies SP during execution.
 * 
 * @param exp - The boolean expression to negate.
 * @return code_seq - The sequence of instructions for the logical NOT.
 */
code_seq gen_code_logical_not_expr(expr_t exp) {
    code_seq ret = gen_code_expr(exp);
    ret = code_seq_concat(ret, code_pop_stack_into_reg(AT, bool_te));

    // Generate instructions for logical NOT.
    ret = code_seq_add_to_end(ret, code_beq(0, AT, 2));  // Skip if false.
    ret = code_seq_add_to_end(ret, code_add(0, 0, AT));  // Set AT to false.
    ret = code_seq_add_to_end(ret, code_beq(0, 0, 1));   // Skip if true.
    ret = code_seq_add_to_end(ret, code_addi(0, AT, 1)); // Set AT to true.

    // Push the result onto the stack.
    return code_seq_concat(ret, code_push_reg_on_stack(AT, bool_te));
}