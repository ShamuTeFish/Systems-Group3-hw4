// $Id: code_utils.c,v 1.13 2024/11/27 23:59:00 leavens Exp $
#include <assert.h>
#include "regname.h"
#include "code.h"
#include "code_seq.h"
#include "code_utils.h"

#define MINIMAL_STACK_ALLOC_IN_WORDS 4
#define SAVED_SP_OFFSET (-1)
#define SAVED_FP_OFFSET (-2)
#define SAVED_STATIC_LINK_OFFSET (-3)
#define SAVED_RA_OFFSET (-4)

/**
 * Copies the value from register `s` to register `t`.
 * If the VM does not support a CPR (copy register) instruction, this function
 * uses the top of the stack as a temporary and modifies SP.
 *
 * @param t - Target register.
 * @param s - Source register.
 * @return code_seq - The sequence of instructions for the operation.
 */
code_seq code_utils_copy_regs(reg_num_type t, reg_num_type s) {
    return code_seq_singleton(code_cpr(t, s));
}

/**
 * Loads the static link (located at `SAVED_STATIC_LINK_OFFSET` in memory
 * relative to register `b`) into register `t`.
 *
 * @param t - Target register.
 * @param b - Base register.
 * @return code_seq - The sequence of instructions for the operation.
 */
code_seq code_utils_load_static_link_into_reg(reg_num_type t, reg_num_type b) {
    return code_seq_singleton(code_lwr(t, b, SAVED_STATIC_LINK_OFFSET));
}

/**
 * Computes the frame pointer (FP) for the given number of scopes outward
 * and stores the result in the specified register.
 *
 * @param reg       - Target register for the frame pointer address.
 * @param levelsOut - Number of scopes outward from the current frame.
 * @return code_seq - The sequence of instructions for the operation.
 */
code_seq code_utils_compute_fp(reg_num_type reg, unsigned int levelsOut) {
    assert(reg != FP && reg != RA);  // Ensure target is not FP or RA.
    code_seq ret = code_utils_copy_regs(reg, FP);  // Start with the current frame.

    while (levelsOut > 0) {
        code_seq_concat(&ret, code_utils_load_static_link_into_reg(reg, reg));
        levelsOut--;
    }

    return ret;
}

/**
 * Allocates the specified number of words on the runtime stack.
 * Updates SP to address the last allocated word.
 *
 * @param words - Number of words to allocate.
 * @return code_seq - The sequence of instructions for the operation.
 */
code_seq code_utils_allocate_stack_space(immediate_type words) {
    assert(words >= 0);
    return code_seq_singleton(code_sri(SP, words));
}

/**
 * Deallocates the specified number of words from the runtime stack.
 * Updates SP to its previous value.
 *
 * @param words - Number of words to deallocate.
 * @return code_seq - The sequence of instructions for the operation.
 */
code_seq code_utils_deallocate_stack_space(immediate_type words) {
    assert(words >= 0);
    return code_seq_singleton(code_ari(SP, words));
}

/**
 * Saves the callee's registers and sets up the runtime stack for a procedure.
 * Modifies SP, FP, RA, and memory from SP to SP - `MINIMAL_STACK_ALLOC_IN_WORDS`.
 *
 * @return code_seq - The sequence of instructions for the operation.
 */
code_seq code_utils_save_registers_for_AR() {
    code_seq ret = code_seq_empty();

    // Save SP, FP, static link, and RA onto the stack.
    code_seq_add_to_end(&ret, code_swr(SP, SAVED_SP_OFFSET, SP));
    code_seq_add_to_end(&ret, code_swr(SP, SAVED_FP_OFFSET, FP));
    code_seq_add_to_end(&ret, code_swr(SP, SAVED_STATIC_LINK_OFFSET, 3));  // $r3 is static link.
    code_seq_add_to_end(&ret, code_swr(SP, SAVED_RA_OFFSET, RA));

    // Update FP to point to the current stack frame.
    code_seq_add_to_end(&ret, code_cpr(FP, SP));

    // Allocate space for the saved registers.
    code_seq_concat(&ret, code_utils_allocate_stack_space(MINIMAL_STACK_ALLOC_IN_WORDS));

    return ret;
}

/**
 * Restores the callee's saved registers from the stack.
 * Restores SP, FP, and RA to their saved values.
 *
 * @return code_seq - The sequence of instructions for the operation.
 */
code_seq code_utils_restore_registers_from_AR() {
    code_seq ret = code_seq_empty();

    // Restore RA, SP (temporarily in $r3), and FP.
    code_seq_add_to_end(&ret, code_lwr(RA, FP, SAVED_RA_OFFSET));
    code_seq_add_to_end(&ret, code_lwr(3, FP, SAVED_SP_OFFSET));
    code_seq_add_to_end(&ret, code_lwr(FP, FP, SAVED_FP_OFFSET));
    code_seq_add_to_end(&ret, code_cpr(SP, 3));  // Restore SP from $r3.

    return ret;
}

/**
 * Sets up the program's runtime stack as if it were in a call (from the OS).
 *
 * @return code_seq - The sequence of instructions for the operation.
 */
code_seq code_utils_set_up_program() {
    code_seq ret = code_utils_copy_regs(3, FP);  // Save FP into $r3.
    code_seq_concat(&ret, code_utils_save_registers_for_AR());
    return ret;
}

/**
 * Tears down the program's runtime stack and exits with exit code 0.
 *
 * @return code_seq - The sequence of instructions for the operation.
 */
code_seq code_utils_tear_down_program() {
    code_seq ret = code_utils_restore_registers_from_AR();
    code_seq_add_to_end(&ret, code_exit(0));  // Exit with code 0.
    return ret;
}
