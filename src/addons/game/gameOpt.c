/**CFile***********************************************************************

   FileName    [gameOpt.c]

   PackageName [game]

   Synopsis    [Option functions of the GAME addon]

   Description []

   SeeAlso     [game.h]

   Author      [Mariotti Alessandro]

   Copyright   [
   This file is part of the ``game'' package of NuGaT.
   Copyright (C) 2010 FBK-irst.

   NuGaT is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 2.1 of the License, or (at your option) any later version.

   NuGaT is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   Lesser General Public License for more details.

   You should have received a copy of the GNU Lesser General Public
   License along with this library; if not, write to the Free Software
   Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307  USA.

   For more information on NuGaT see <http://es.fbk.eu/tools/nugat>
   or email to <nugat-users@list.fbk.eu>.
   Please report bugs to <nugat-users@list.fbk.eu>.

   To contact the NuGaT development board, email to <nugat@list.fbk.eu>. ]

******************************************************************************/

#if HAVE_CONFIG_H
# include "config.h"
#endif

#include "game.h"
#include "gameInt.h"
#include "opt/opt.h"
#include "utils/utils.h"
#include "nusmv/core/utils/StreamMgr.h"
#include "nusmv/core/cinit/NuSMVEnv.h"

/*---------------------------------------------------------------------------*/
static char rcsid[] UTIL_UNUSED = "$Id$";
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Type declarations                                                         */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Variable declarations                                                     */
/*---------------------------------------------------------------------------*/
EXTERN FILE* nusmv_stderr;
EXTERN FILE* nusmv_stdout;

/*---------------------------------------------------------------------------*/
/* Static function prototypes                                                */
/*---------------------------------------------------------------------------*/

static void * game_opt_get_string ARGS((OptsHandler_ptr opts,
                                        const char *value));

static boolean game_opt_check_initial_condition ARGS((OptsHandler_ptr opt,
                                                      const char* value));
/*---------------------------------------------------------------------------*/
/* Definition of exported functions                                          */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

   Synopsis    [Initializes game addon options]

   Description [Initializes game addon options]

   SideEffects []

   SeeAlso     []

******************************************************************************/
void Game_init_opt(NuSMVEnv_ptr env)
{
  OptsHandler_ptr opt = NuSMVEnv_get_value(env, ENV_OPTS_HANDLER);
  boolean res = true;
  boolean options_registered;

  options_registered =
    OptsHandler_is_option_registered(opt, GAME_OPT_INITIALIZED) &&
    OptsHandler_get_bool_option_value(opt, GAME_OPT_INITIALIZED);

  /* If options are registered, do not register them again */
  if (options_registered) return;

  res = OptsHandler_register_bool_option(opt, GAME_GAME, false, false);
  nusmv_assert(res);

  res = OptsHandler_register_bool_option(opt, GAME_PRINT_PLAN,
                                         false, true);
  nusmv_assert(res);

  res = OptsHandler_register_option(opt, GAME_GAME_INITIAL_CONDITION, "N",
                             (Opts_CheckFnType)game_opt_check_initial_condition,
                                    (Opts_ReturnFnType)game_opt_get_string,
                                    true, GENERIC_OPTION,env);
  nusmv_assert(res);

  res = OptsHandler_register_generic_option(opt, GAME_SF07_GBA_WRING_BINARY,
                                            DEFAULT_GAME_SF07_GBA_WRING_BINARY,
                                            true);
  nusmv_assert(res);

  res = OptsHandler_register_bool_option(opt, GAME_SF07_GBA_WRING_HAS_CC,
                                         DEFAULT_GAME_SF07_GBA_WRING_HAS_CC,
                                         true);
  nusmv_assert(res);

  res = OptsHandler_register_generic_option(opt, GAME_SF07_GBA_WRING_INPUT_DIR,
                                          DEFAULT_GAME_SF07_GBA_WRING_INPUT_DIR,
                                            true);
  nusmv_assert(res);

  res = OptsHandler_register_generic_option(opt, GAME_SF07_GBA_WRING_INPUT_TEMPL,
                                        DEFAULT_GAME_SF07_GBA_WRING_INPUT_TEMPL,
                                            true);
  nusmv_assert(res);

  res = OptsHandler_register_bool_option(opt, GAME_SF07_GBA_WRING_INPUT_KEEP,
                                         false, true);
  nusmv_assert(res);

  res = OptsHandler_register_generic_option(opt, GAME_SF07_GBA_WRING_OUTPUT_DIR,
                                         DEFAULT_GAME_SF07_GBA_WRING_OUTPUT_DIR,
                                            true);
  nusmv_assert(res);

  res = OptsHandler_register_generic_option(opt,
                                            GAME_SF07_GBA_WRING_OUTPUT_TEMPL,
                                       DEFAULT_GAME_SF07_GBA_WRING_OUTPUT_TEMPL,
                                            true);
  nusmv_assert(res);

  res = OptsHandler_register_bool_option(opt, GAME_SF07_GBA_WRING_OUTPUT_KEEP,
                                         false, true);
  nusmv_assert(res);

  {
    Opts_EnumRec game_sf07_strategy_printing_modes[3] = {
      {GAME_SF07_STRATEGY_PRINTING_MODE_SEXP_STRING,
       GAME_SF07_STRATEGY_PRINTING_MODE_SEXP},
      {GAME_SF07_STRATEGY_PRINTING_MODE_BDD_SEPARATE_STRING,
       GAME_SF07_STRATEGY_PRINTING_MODE_BDD_SEPARATE},
      {GAME_SF07_STRATEGY_PRINTING_MODE_BDD_CONJOINED_STRING,
       GAME_SF07_STRATEGY_PRINTING_MODE_BDD_CONJOINED},
    };
    res = OptsHandler_register_enum_option(opt,
                                           GAME_SF07_STRATEGY_PRINTING_MODE,
                                   GAME_SF07_STRATEGY_PRINTING_MODE_SEXP_STRING,
                                           game_sf07_strategy_printing_modes,
                                           3,
                                           true);
    nusmv_assert(res);
  }

  /* Flag the GAME options as initialized */
  res = OptsHandler_register_bool_option(opt, GAME_OPT_INITIALIZED, true, false);
  nusmv_assert(res);
}

boolean opt_game_game(OptsHandler_ptr opt)
{
  return OptsHandler_get_bool_option_value(opt, GAME_GAME);
}

void set_game_game(OptsHandler_ptr opt)
{
  boolean res = OptsHandler_set_bool_option_value(opt, GAME_GAME, true);
  nusmv_assert(res);
}
void unset_game_game(OptsHandler_ptr opt)
{
  boolean res = OptsHandler_set_bool_option_value(opt, GAME_GAME, false);
  nusmv_assert(res);
}
/* enables printing a strategy when it is found */
void set_game_print_strategy(OptsHandler_ptr opt)
{
  boolean res = OptsHandler_set_bool_option_value(opt, GAME_PRINT_PLAN, true);
  nusmv_assert(res);
}
void unset_game_print_strategy(OptsHandler_ptr opt)
{
  boolean res = OptsHandler_set_bool_option_value(opt, GAME_PRINT_PLAN, false);
  nusmv_assert(res);
}
boolean opt_game_print_strategy(OptsHandler_ptr opt)
{
  return OptsHandler_get_bool_option_value(opt, GAME_PRINT_PLAN);
}
/* defines how initial condition are interpreted in a game */
void set_game_game_initial_condition(OptsHandler_ptr opt, char c)
{
  boolean res = OptsHandler_set_int_option_value(opt,
                                                 GAME_GAME_INITIAL_CONDITION,
                                                 (int)c);
  nusmv_assert(res);
}
void unset_game_game_initial_condition(OptsHandler_ptr opt)
{
  boolean res = OptsHandler_reset_option_value(opt, GAME_GAME_INITIAL_CONDITION);
  nusmv_assert(res);
}
char opt_game_game_initial_condition(OptsHandler_ptr opt)
{
  /* Value correctness is checked by the checking function.. */
  char* val = OptsHandler_get_option_value(opt, GAME_GAME_INITIAL_CONDITION);
  return val[0];
}
void set_game_sf07_strategy_printing_mode(OptsHandler_ptr opt,
                                          Game_SF07_StrategyPrintingMode m)
{
  const char* str = Game_SF07_StrategyPrintingMode_to_string(m);
  boolean res = OptsHandler_set_option_value(opt,
                                             GAME_SF07_STRATEGY_PRINTING_MODE,
                                             str);
  nusmv_assert(res);
}
Game_SF07_StrategyPrintingMode
get_game_sf07_strategy_printing_mode(OptsHandler_ptr opt)
{
  int res;
  res = OptsHandler_get_enum_option_value(opt, GAME_SF07_STRATEGY_PRINTING_MODE);
  return (Game_SF07_StrategyPrintingMode) res;
}
void reset_game_sf07_strategy_printing_mode(OptsHandler_ptr opt)
{
  boolean res = OptsHandler_reset_option_value(opt,
                                               GAME_SF07_STRATEGY_PRINTING_MODE);
  nusmv_assert(res);
}
void set_game_sf07_gba_wring_binary(OptsHandler_ptr opt, char* str)
{
  boolean res = OptsHandler_set_option_value(opt,
                                             GAME_SF07_GBA_WRING_BINARY,
                                             str);
  nusmv_assert(res);
}
void reset_game_sf07_gba_wring_binary(OptsHandler_ptr opt)
{
  boolean res = OptsHandler_reset_option_value(opt, GAME_SF07_GBA_WRING_BINARY);
  nusmv_assert(res);
}
char* get_game_sf07_gba_wring_binary(OptsHandler_ptr opt)
{
  return OptsHandler_get_string_option_value(opt, GAME_SF07_GBA_WRING_BINARY);
}
void set_game_sf07_gba_wring_has_cc(OptsHandler_ptr opt)
{
  boolean res = OptsHandler_set_bool_option_value(opt,
                                                  GAME_SF07_GBA_WRING_HAS_CC,
                                                  true);
  nusmv_assert(res);
}
void unset_game_sf07_gba_wring_has_cc(OptsHandler_ptr opt)
{
  boolean res = OptsHandler_set_bool_option_value(opt,
                                                  GAME_SF07_GBA_WRING_HAS_CC,
                                                  false);
  nusmv_assert(res);
}
boolean opt_game_sf07_gba_wring_has_cc(OptsHandler_ptr opt)
{
  return OptsHandler_get_bool_option_value(opt, GAME_SF07_GBA_WRING_HAS_CC);
}

void set_game_sf07_gba_wring_input_dir(OptsHandler_ptr opt, char* str)
{
  boolean res = OptsHandler_set_option_value(opt, GAME_SF07_GBA_WRING_INPUT_DIR,
                                             str);
  nusmv_assert(res);
}
void reset_game_sf07_gba_wring_input_dir(OptsHandler_ptr opt)
{
  boolean res = OptsHandler_reset_option_value(opt,
                                               GAME_SF07_GBA_WRING_INPUT_DIR);
  nusmv_assert(res);
}

char* get_game_sf07_gba_wring_input_dir(OptsHandler_ptr opt)
{
  return OptsHandler_get_string_option_value(opt, GAME_SF07_GBA_WRING_INPUT_DIR);
}

void set_game_sf07_gba_wring_input_templ(OptsHandler_ptr opt, char* str)
{
  boolean res = OptsHandler_set_option_value(opt,
                                             GAME_SF07_GBA_WRING_INPUT_TEMPL,
                                             str);
  nusmv_assert(res);
}
void reset_game_sf07_gba_wring_input_templ(OptsHandler_ptr opt)
{
  boolean res = OptsHandler_reset_option_value(opt,
                                               GAME_SF07_GBA_WRING_INPUT_TEMPL);
  nusmv_assert(res);
}

char* get_game_sf07_gba_wring_input_templ(OptsHandler_ptr opt)
{
  return OptsHandler_get_string_option_value(opt,
                                             GAME_SF07_GBA_WRING_INPUT_TEMPL);
}

void set_game_sf07_gba_wring_input_keep(OptsHandler_ptr opt)
{
  boolean res = OptsHandler_set_bool_option_value(opt,
                                                  GAME_SF07_GBA_WRING_INPUT_KEEP,
                                                  true);
  nusmv_assert(res);
}
void unset_game_sf07_gba_wring_input_keep(OptsHandler_ptr opt)
{
  boolean res = OptsHandler_set_bool_option_value(opt,
                                                  GAME_SF07_GBA_WRING_INPUT_KEEP,
                                                  false);
  nusmv_assert(res);
}
boolean opt_game_sf07_gba_wring_input_keep(OptsHandler_ptr opt)
{
  return OptsHandler_get_bool_option_value(opt, GAME_SF07_GBA_WRING_INPUT_KEEP);
}

void set_game_sf07_gba_wring_output_dir(OptsHandler_ptr opt, char* str)
{
  boolean res = OptsHandler_set_option_value(opt, GAME_SF07_GBA_WRING_OUTPUT_DIR,
                                             str);
  nusmv_assert(res);
}
void reset_game_sf07_gba_wring_output_dir(OptsHandler_ptr opt)
{
  boolean res = OptsHandler_reset_option_value(opt,
                                               GAME_SF07_GBA_WRING_OUTPUT_DIR);
  nusmv_assert(res);
}

char* get_game_sf07_gba_wring_output_dir(OptsHandler_ptr opt)
{
  return OptsHandler_get_string_option_value(opt,
                                             GAME_SF07_GBA_WRING_OUTPUT_DIR);
}

void set_game_sf07_gba_wring_output_templ(OptsHandler_ptr opt, char* str)
{
  boolean res = OptsHandler_set_option_value(opt,
                                             GAME_SF07_GBA_WRING_OUTPUT_TEMPL,
                                             str);
  nusmv_assert(res);
}
void reset_game_sf07_gba_wring_output_templ(OptsHandler_ptr opt)
{
  boolean res = OptsHandler_reset_option_value(opt,
                                               GAME_SF07_GBA_WRING_OUTPUT_TEMPL);
  nusmv_assert(res);
}

char* get_game_sf07_gba_wring_output_templ(OptsHandler_ptr opt)
{
  return OptsHandler_get_string_option_value(opt,
                                             GAME_SF07_GBA_WRING_OUTPUT_TEMPL);
}

void set_game_sf07_gba_wring_output_keep(OptsHandler_ptr opt)
{
  boolean res = OptsHandler_set_bool_option_value(opt,
                                                GAME_SF07_GBA_WRING_OUTPUT_KEEP,
                                                  true);
  nusmv_assert(res);
}
void unset_game_sf07_gba_wring_output_keep(OptsHandler_ptr opt)
{
  boolean res = OptsHandler_set_bool_option_value(opt,
                                                GAME_SF07_GBA_WRING_OUTPUT_KEEP,
                                                  false);
  nusmv_assert(res);
}
boolean opt_game_sf07_gba_wring_output_keep(OptsHandler_ptr opt)
{
  return OptsHandler_get_bool_option_value(opt, GAME_SF07_GBA_WRING_OUTPUT_KEEP);
}


/*---------------------------------------------------------------------------*/
/* Definition of static functions                                            */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

   Synopsis           [Get the integer representation of the given string]

   Description        [Get the integer representation of the given string]

   SideEffects        []

   SeeAlso            []

******************************************************************************/
static void * game_opt_get_string(OptsHandler_ptr opts, const char *value)
{
  return (void*)value;
}

/**Function********************************************************************

   Synopsis    [Checks if the given initial condition is correct]

   Description [Checks if the given initial condition is correct]

   SideEffects []

   SeeAlso     []

******************************************************************************/
static boolean game_opt_check_initial_condition(OptsHandler_ptr opt,
                                                const char* value)
{
  char* val = (char*)game_opt_get_string(opt, value);

  if (strlen(val) == 1 && (val[0] == 'N' || val[0] == 'A' || val[0] == 'E')) {
    return true;
  }

  FREE(val);
  fprintf(nusmv_stderr,
          "Error: supplied an invalid interpretation of game initial "
          "conditions.\n"
          "Possible values: N, A and E.\n"
          "  N : normal -- every player chooses initial values only for its "
          "variables;\n"
          "  E : existential -- a player a game is played for chooses an "
          "initial state;\n"
          "  A : universal -- an opponent chooses an initial state.\n"
          );

  return false;
}
