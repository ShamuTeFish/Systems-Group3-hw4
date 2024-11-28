/* $Id: gen_code.h,v 1.8 2024/11/27 23:59:00 leavens Exp $ */
#ifndef _GEN_CODE_H
#define _GEN_CODE_H

#include <stdio.h>
#include "ast.h"
#include "bof.h"
#include "instruction.h"
#include "code.h"
#include "code_seq.h"

/* === Initialization === */

/**
 * Initializes the code generator.
 * Prepares necessary structures such as the literal table for managing constants.
 */
extern void gen_code_initialize();

/* === Main Code Generation === */

/**
 * Generates machine code for the program's AST and writes it to a binary object file.
 *
 * @param bf   - The binary object file, open for writing in binary mode.
 * @param prog - The program's abstract syntax tree (AST).
 */
extern void gen_code_program(BOFFILE bf, block_t prog);

/* === Variable Declarations === */

/**
 * Generates code for variable declarations.
 * For each declared identifier, generates two instructions:
 * - One to allocate space on the stack.
 * - Another to initialize the allocated space (e.g., to 0 for variables).
 *
 * @param vds - The variable declarations AST node.
 * @return code_seq - The generated sequence of instructions.
 */
extern code_seq gen_code_var_decls(var_decls_t vds);

/**
 * Generates code for a single variable declaration.
 * Follows the same principle as `gen_code_var_decls` for one identifier.
 *
 * @param vd - The single variable declaration AST node.
 * @return code_seq - The generated sequence of instructions.
 */
extern code_seq gen_code_var_decl(var_decl_t vd);

/**
 * Generates code for identifiers in the list, with a specified type.
 * The code is generated in reverse order (first declared are allocated last).
 * Each identifier generates two instructions:
 * - One to allocate space on the stack.
 * - Another to initialize the allocated space.
 *
 * @param idents - The list of identifiers to generate code for.
 * @param t      - The type of the identifiers (e.g., constants or variables).
 * @return code_seq - The generated sequence of instructions.
 */
extern code_seq gen_code_idents(ident_list_t idents, AST_type t);

/* === Statements === */

/**
 * Generates code for a given statement.
 * Dispatches to the appropriate function based on the statement type.
 *
 * @param stmt - The statement AST node.
 * @return code_seq - The generated sequence of instructions.
 */
extern code_seq gen_code_stmt(stmt_t stmt);

/**
 * Generates code for an assignment statement.
 * Computes the expression and stores its result in the assigned variable.
 *
 * @param stmt - The assignment statement AST node.
 * @return code_seq - The generated sequence of instructions.
 */
extern code_seq gen_code_assign_stmt(assign_stmt_t stmt);

/**
 * Generates code for a list of statements.
 * Processes each statement in sequence and concatenates the generated code.
 *
 * @param stmts - The list of statements AST node.
 * @return code_seq - The generated sequence of instructions.
 */
extern code_seq gen_code_stmts(stmts_t stmts);

/**
 * Generates code for an if statement.
 * Evaluates the condition and executes the body if the condition is true.
 *
 * @param stmt - The if statement AST node.
 * @return code_seq - The generated sequence of instructions.
 */
extern code_seq gen_code_if_stmt(if_stmt_t stmt);

/**
 * Generates code for a while statement.
 * Continuously evaluates the condition and executes the body while true.
 *
 * @param stmt - The while statement AST node.
 * @return code_seq - The generated sequence of instructions.
 */
extern code_seq gen_code_while_stmt(while_stmt_t stmt);

/**
 * Generates code for a read statement.
 * Reads input and assigns it to the specified variable.
 *
 * @param stmt - The read statement AST node.
 * @return code_seq - The generated sequence of instructions.
 */
extern code_seq gen_code_read_stmt(read_stmt_t stmt);

/**
 * Generates code for a print statement.
 * Evaluates the expression and outputs the result.
 *
 * @param stmt - The print statement AST node.
 * @return code_seq - The generated sequence of instructions.
 */
extern code_seq gen_code_print_stmt(print_stmt_t stmt);

/* === Expressions === */

/**
 * Generates code for an expression.
 * Evaluates the expression and places the result on the stack.
 *
 * @param exp - The expression AST node.
 * @return code_seq - The generated sequence of instructions.
 */
extern code_seq gen_code_expr(expr_t exp);

/**
 * Generates code for a binary operation expression.
 * Applies the operation to two sub-expressions and pushes the result.
 *
 * @param exp - The binary operation expression AST node.
 * @return code_seq - The generated sequence of instructions.
 */
extern code_seq gen_code_binary_op_expr(binary_op_expr_t exp);

/**
 * Generates code to apply an operator to the top two elements of the stack.
 * The result is pushed back onto the stack.
 *
 * @param op   - The operator token (e.g., +, -, <, >).
 * @param typ  - The type of the operands (e.g., float, integer).
 * @return code_seq - The generated sequence of instructions.
 */
extern code_seq gen_code_op(token_t op, AST_type typ);

/**
 * Generates code for a logical NOT operation.
 * Negates a boolean expression and pushes the result on the stack.
 *
 * @param exp - The boolean expression AST node.
 * @return code_seq - The generated sequence of instructions.
 */
extern code_seq gen_code_logical_not_expr(expr_t exp);

/* === Arithmetic and Relational Operations === */

/**
 * Generates code for a floating-point arithmetic operation.
 * Applies the operation to the top two elements of the stack.
 *
 * @param arith_op - The arithmetic operator token (e.g., +, -, *, /).
 * @return code_seq - The generated sequence of instructions.
 */
extern code_seq gen_code_arith_op(token_t arith_op);

/**
 * Generates code for a relational comparison.
 * Compares the top two elements of the stack and pushes the result as a boolean value.
 *
 * @param rel_op - The relational operator token (e.g., <, >, ==, !=).
 * @param typ    - The type of the operands (e.g., float, integer).
 * @return code_seq - The generated sequence of instructions.
 */
extern code_seq gen_code_rel_op(token_t rel_op, AST_type typ);

/* === Identifiers and Constants === */

/**
 * Generates code to load the value of an identifier onto the stack.
 * Uses temporary registers and modifies the stack pointer during execution.
 *
 * @param id - The identifier AST node.
 * @return code_seq - The generated sequence of instructions.
 */
extern code_seq gen_code_ident(ident_t id);

/**
 * Generates code to load a numeric constant onto the stack.
 * Uses temporary registers during execution.
 *
 * @param num - The numeric constant AST node.
 * @return code_seq - The generated sequence of instructions.
 */
extern code_seq gen_code_number(number_t num);

#endif /* _GEN_CODE_H */
