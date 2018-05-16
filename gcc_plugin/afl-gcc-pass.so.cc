/*
   american fuzzy lop - GCC instrumentation pass
   ---------------------------------------------

   Written by Austin Seipp <aseipp@pobox.com> with bits from
              Emese Revfy <re.emese@gmail.com>

   Updated by Thorsten Schulz <thorsten.schulz@uni-rostock.de>

   GCC integration design is based on the LLVM design, which comes
   from Laszlo Szekeres. Some of the boilerplate code below for
   afl_pass to adapt to different GCC versions was taken from Emese
   Revfy's Size Overflow plugin for GCC, licensed under the GPLv2/v3.

   (NOTE: this plugin code is under GPLv3, in order to comply with the
   GCC runtime library exception, which states that you may distribute
   "Target Code" from the compiler under a license of your choice, as
   long as the "Compilation Process" is "Eligible", and contains no
   GPL-incompatible software in GCC "during the process of
   transforming high level code to target code". In this case, the
   plugin will be used to generate "Target Code" during the
   "Compilation Process", and thus it must be GPLv3 to be "eligible".)

   Copyright (C) 2015 Austin Seipp

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <http://www.gnu.org/licenses/>.

 */

#include "../config.h"
#include "../debug.h"

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

#include <gcc-plugin.h>
#include <plugin-version.h>
#include <diagnostic.h>
#include <tree.h>
#include <tree-ssa.h>
#include <tree-pass.h>
#include <gimple.h>
#include <gimple-iterator.h>
#include <version.h>
#include <toplev.h>
#include <intl.h>
#include <context.h>
#include <stringpool.h>

/* Eclipse Hack */
#ifndef VERSION
#define VERSION "X"
#endif

/* -------------------------------------------------------------------------- */
/* -- AFL instrumentation pass ---------------------------------------------- */

static int be_quiet = 0;
static unsigned int inst_ratio = 100;
static int inst_blocks = 0;

static unsigned int ext_call_instrument(function *fun) {
	/* Instrument all the things! */
	basic_block bb;
	unsigned finst_blocks = 0;
	unsigned fcnt_blocks = 0;

	FOR_ALL_BB_FN(bb, fun) {
		gimple *fcall = NULL;
		gimple_seq seq = NULL;
		gimple_stmt_iterator bentry;

		fcnt_blocks++;

		/* Bail on this block if we trip the specified ratio */
		if (R(100) >= inst_ratio) continue;

		/* Make up cur_loc */

		unsigned int rand_loc = R(MAP_SIZE);
		tree cur_loc = build_int_cst(uint64_type_node, rand_loc);

		/* Update bitmap via external call */
		/* to quote:
		 * /+ Trace a basic block with some ID +/
		 * void __afl_trace(u16 x);
		 */

		tree fntype = build_function_type_list(
			void_type_node,   /* return */
			uint16_type_node, /* args */
			NULL_TREE);       /* done */
		tree fndecl = build_fn_decl("__afl_trace", fntype);
		TREE_STATIC(fndecl)     = 1; /* Defined elsewhere */
		TREE_PUBLIC(fndecl)     = 1; /* Public */
		DECL_EXTERNAL(fndecl)   = 1; /* External linkage */
		DECL_ARTIFICIAL(fndecl) = 1; /* Injected by compiler */

		fcall = gimple_build_call(fndecl, 1, cur_loc);  /* generate the function _call_ to above built reference, with *1* parameter -> the random const for the location */
		//gimple_seq_add_stmt(&seq, fcall); /* and insert into a sequence */

		/* Done - grab the entry to the block and insert sequence */
		bentry = gsi_start_bb(bb);
		gsi_insert_seq_before(&bentry, seq, GSI_SAME_STMT);

		inst_blocks++;
		finst_blocks++;
	}

	/* Say something nice. */
	if (!be_quiet) {
		if (!finst_blocks)
			WARNF(G_("No instrumentation targets found in " cBRI "%s" cRST ),
					function_name(fun));
		else if (finst_blocks < fcnt_blocks)
			OKF(G_("Instrumented %2u /%2u locations in " cBRI "%s" cRST ),
					finst_blocks, fcnt_blocks,
					function_name(fun));
		else
			OKF(G_("Instrumented   %2u   locations in " cBRI "%s" cRST ),
					finst_blocks,
					function_name(fun));
	}

	return 0;
}

static unsigned int inline_instrument(function *fun) {
	/* Instrument all the things! */
	basic_block bb;

	/* Set up global type declarations */
	tree map_type = build_pointer_type(unsigned_char_type_node);
	tree map_ptr_g = build_decl(BUILTINS_LOCATION, VAR_DECL,
			get_identifier("__afl_area_ptr"), map_type);
	TREE_USED(map_ptr_g) = 1;
	TREE_STATIC(map_ptr_g) = 1; /* Defined elsewhere */
	DECL_EXTERNAL(map_ptr_g) = 1; /* External linkage */
	DECL_PRESERVE_P(map_ptr_g) = 1;
	DECL_ARTIFICIAL(map_ptr_g) = 1;
	rest_of_decl_compilation(map_ptr_g, 1, 0);

	tree prev_loc_g = build_decl(BUILTINS_LOCATION, VAR_DECL,
			get_identifier("__afl_prev_loc"), uint16_type_node);
	TREE_USED(prev_loc_g) = 1;
	TREE_STATIC(prev_loc_g) = 1; /* Defined elsewhere */
	DECL_EXTERNAL(prev_loc_g) = 1; /* External linkage */
	DECL_PRESERVE_P(prev_loc_g) = 1;
	DECL_ARTIFICIAL(prev_loc_g) = 1;
	rest_of_decl_compilation(prev_loc_g, 1, 0);

	FOR_ALL_BB_FN(bb, fun) {
		gimple *g;
		gimple_seq seq = NULL;
		gimple_stmt_iterator bentry;

		/* Bail on this block if we trip the specified ratio */

		if (R(100) >= inst_ratio)
			continue;

		/* Make up cur_loc */

		unsigned int rand_loc = R(MAP_SIZE);
		tree cur_loc = build_int_cst(uint64_type_node, rand_loc);

		/* Load prev_loc, xor with cur_loc */

		tree area_off = create_tmp_var(uint64_type_node, "area_off");
		g = gimple_build_assign(area_off, BIT_XOR_EXPR, prev_loc_g, cur_loc);
		gimple_seq_add_stmt(&seq, g); // area_off = prev_loc ^ cur_loc

		/* Update bitmap */

		tree zero = build_int_cst(unsigned_char_type_node, 0);
		tree one = build_int_cst(unsigned_char_type_node, 1);

		tree tmp1 = create_tmp_var(map_type, "tmp1");
		g = gimple_build_assign(tmp1, PLUS_EXPR, map_ptr_g, area_off);
		gimple_seq_add_stmt(&seq, g); // tmp1 = __afl_area_ptr + area_off

		tree tmp2 = create_tmp_var(unsigned_char_type_node, "tmp2");
		tree deref1 = build_fold_indirect_ref(tmp1);
		g = gimple_build_assign(tmp2, INIT_EXPR, deref1);
		gimple_seq_add_stmt(&seq, g); // tmp2 = *tmp1

		tree tmp3 = create_tmp_var(unsigned_char_type_node, "tmp3");
		g = gimple_build_assign(tmp3, PLUS_EXPR, tmp2, one);
		gimple_seq_add_stmt(&seq, g); // tmp3 = tmp2 + 1

		tree tmp4 = create_tmp_var(map_type, "tmp4");
		g = gimple_build_assign(tmp4, PLUS_EXPR, map_ptr_g, area_off);
		gimple_seq_add_stmt(&seq, g); // tmp4 = __afl_area_ptr + area_off

		tree deref2 = build2(MEM_REF, map_type, tmp4, zero);
		g = gimple_build_assign(deref2, MODIFY_EXPR, tmp3);
		//gimple_seq_add_stmt(&seq, g); // *tmp4 = tmp3

		/* Set prev_loc to cur_loc >> 1 */

		tree shifted_loc = build_int_cst(TREE_TYPE(prev_loc_g), rand_loc >> 1);
		g = gimple_build_assign(prev_loc_g, MODIFY_EXPR, shifted_loc);
		gimple_seq_add_stmt(&seq, g); // __afl_pred_loc = cur_loc >> 1

		/* Done - grab the entry to the block and insert sequence */

		bentry = gsi_start_bb(bb);
		gsi_insert_seq_before(&bentry, seq, GSI_SAME_STMT);

		inst_blocks++;
	}

	/* Say something nice. */
	if (!be_quiet) {
		if (!inst_blocks)
			WARNF(G_("No instrumentation targets found."));
		else
			OKF(G_("Instrumented %u locations (%s mode, ratio %u%%)."),
					inst_blocks,
					getenv("AFL_HARDEN") ? G_("hardened") : G_("non-hardened"),
					inst_ratio);
	}

	return 0;
}


/* -------------------------------------------------------------------------- */
/* -- Boilerplate and initialization ---------------------------------------- */

static const struct pass_data afl_pass_data = {

                .type                   = GIMPLE_PASS,
                .name                   = "afl-inst",
                .optinfo_flags          = OPTGROUP_NONE,

                .tv_id                  = TV_NONE,
                .properties_required    = 0,
                .properties_provided    = 0,
                .properties_destroyed   = 0,
                .todo_flags_start       = 0,
                // NOTE(aseipp): it's very, very important to include
                // at least 'TODO_update_ssa' here so that GCC will
                // properly update the resulting SSA form, e.g., to
                // include new PHI nodes for newly added symbols or
                // names. Do not remove this. Do not taunt Happy Fun
                // Ball.
                .todo_flags_finish      = TODO_update_ssa | TODO_verify_il | TODO_cleanup_cfg,
};

namespace {

class afl_pass : public gimple_opt_pass {
private:
	bool do_ext_call;

public:
	afl_pass(bool ext_call, gcc::context *g) : gimple_opt_pass(afl_pass_data, g), do_ext_call(ext_call) {}

	virtual unsigned int execute(function *fun) {
		return do_ext_call ? ext_call_instrument(fun) : inline_instrument(fun);
	}
}; /* class afl_pass */

}  /* anon namespace */

static struct opt_pass *make_afl_pass(bool ext_call, gcc::context *ctxt) {
	return new afl_pass(ext_call, ctxt);
}

/* -------------------------------------------------------------------------- */
/* -- Initialization -------------------------------------------------------- */

int plugin_is_GPL_compatible = 1;

static struct plugin_info afl_plugin_info = {
  .version = "20180600",
  .help    = "AFL gcc plugin\n",
};

int plugin_init(struct plugin_name_args *plugin_info,
                struct plugin_gcc_version *version) {

	const char * const pname = plugin_info->base_name;
	struct register_pass_info afl_pass_info;
	struct timeval tv;
	struct timezone tz;
	u32 rand_seed;

	/* Setup random() so we get Actually Random(TM) outputs from R() */
	gettimeofday(&tv, &tz);
	rand_seed = tv.tv_sec ^ tv.tv_usec ^ getpid();
	srandom(rand_seed);

	/* Pass information */
	afl_pass_info.pass = make_afl_pass(true, g);
	afl_pass_info.reference_pass_name = "ssa";
	afl_pass_info.ref_pass_instance_number = 1;
	afl_pass_info.pos_op = PASS_POS_INSERT_AFTER;

	if (!plugin_default_version_check(version, &gcc_version)) {
		FATAL(G_("Incompatible gcc/plugin versions!"));
	}

	/* Show a banner */
	if (isatty(2) && !getenv("AFL_QUIET")) {
		SAYF(G_(cCYA "afl-gcc-pass " cBRI VERSION cRST " by <aseipp@pobox.com>, updated by <thorsten.schulz@uni-rostock.de>\n"));
	} else
		be_quiet = 1;

	/* Decide instrumentation ratio */
	char* inst_ratio_str = getenv("AFL_INST_RATIO");

	if (inst_ratio_str) {
		if (sscanf(inst_ratio_str, "%u", &inst_ratio) != 1 || !inst_ratio || inst_ratio > 100)
			FATAL(G_("Bad value of AFL_INST_RATIO (must be between 1 and 100)"));
		else {
			if (!be_quiet)
				ACTF(G_("Instrumention ratio %u%% in %s mode."),
					inst_ratio,
					getenv("AFL_HARDEN") ? G_("hardened") : G_("non-hardened"));
		}
	}

	/* Go go gadget */
	register_callback(pname, PLUGIN_INFO, NULL, &afl_plugin_info);
	register_callback(pname, PLUGIN_PASS_MANAGER_SETUP, NULL, &afl_pass_info);
	return 0;
}
