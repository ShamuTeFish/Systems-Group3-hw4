/* $Id: code_seq.h,v 1.4 2024/11/27 23:59:00 leavens Exp $ */
#ifndef _CODE_SEQ_H
#define _CODE_SEQ_H

#include <stdbool.h>
#include "code.h"

/**
 * A code sequence represents a linked list of instructions, 
 * with an additional pointer to the last node for efficient concatenation.
 */
typedef struct {
    code *first;  ///< Pointer to the first instruction.
    code *last;   ///< Pointer to the last instruction.
} code_seq;

/**
 * Creates an empty code sequence.
 *
 * @return code_seq - An empty code sequence.
 */
extern code_seq code_seq_empty();

/**
 * Creates a code sequence containing a single instruction.
 *
 * @param c - The instruction to include in the sequence.
 * @return code_seq - A code sequence with one instruction.
 */
extern code_seq code_seq_singleton(code *c);

/**
 * Checks if the given code sequence is empty.
 *
 * @param seq - The code sequence to check.
 * @return bool - True if the sequence is empty, false otherwise.
 */
extern bool code_seq_is_empty(code_seq seq);

/**
 * Retrieves the first instruction from a non-empty code sequence.
 *
 * @param seq - The code sequence.
 * @return code* - The first instruction in the sequence.
 */
extern code *code_seq_first(code_seq seq);

/**
 * Retrieves a new code sequence containing all instructions except the first.
 * The original sequence is not modified.
 *
 * @param seq - The code sequence.
 * @return code_seq - The new sequence.
 */
extern code_seq code_seq_rest(code_seq seq);

/**
 * Retrieves the size (number of instructions) of a code sequence.
 *
 * @param seq - The code sequence.
 * @return unsigned int - The size of the sequence.
 */
extern unsigned int code_seq_size(code_seq seq);

/**
 * Retrieves the last instruction from a non-empty code sequence.
 *
 * @param seq - The code sequence.
 * @return code* - The last instruction in the sequence.
 */
extern code *code_seq_last_elem(code_seq seq);

/**
 * Adds a new instruction to the end of a code sequence.
 *
 * @param seq - The code sequence to modify.
 * @param c   - The instruction to add.
 */
extern void code_seq_add_to_end(code_seq *seq, code *c);

/**
 * Concatenates two code sequences.
 * The second sequence is appended to the first.
 *
 * @param s1 - The first code sequence (modified).
 * @param s2 - The second code sequence.
 */
extern void code_seq_concat(code_seq *s1, code_seq s2);

/**
 * Prints the instructions in a code sequence in assembly format.
 *
 * @param out - The output file.
 * @param seq - The code sequence to print.
 */
extern void code_seq_debug_print(FILE *out, code_seq seq);

#endif
