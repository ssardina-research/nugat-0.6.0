/**CFile***********************************************************************

  FileName    [ gameCheckLTLSF07_gba_wring.c ]

  PackageName [ game ]

  Synopsis    [ Implements a simple interface to the Wring LTL to
                generalized B\"uchi automaton translator. ]

  Description [ ]

  SeeAlso     [ ]

  Author      [ Viktor Schuppan ]

  Copyright   [
  This file is part of the ``game'' package of NuGaT.
  Copyright (C) 2010 by FBK-irst.

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

#include "gameCheckLTLSF07_gba_wring.h"
#include "gameCheckLTLSF07_gba.h"

#include "addons/game/gameInt.h"
#include "node/node.h"
#include "opt/opt.h"
#include "parser/symbols.h"
#include "utils/Slist.h"
#include "utils/error.h"
#include "utils/utils.h"

#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <code/nusmv/core/utils/ErrorMgr.h>

static char rcsid[] UTIL_UNUSED = "$Id: gameCheckLTLSF07_gba_wring.c,v 1.1.2.5 2010-01-15 04:40:05 nusmv Exp $";

/*---------------------------------------------------------------------------*/
/* Structure declarations                                                    */
/*---------------------------------------------------------------------------*/

/**Struct**********************************************************************

  Synopsis    [ Interface to Wring. ]

  Description [ Fields:

                formula - the input formula;

                gba - the resulting B\"uchi automaton;

                binary_file_name - the full path of the Wring binary;

                input_file_name - the full path of the file for the
                  input to Wring;

                output_file_name - the full path of the file for the
                  output of Wring;

                For the input writer:

                input_file - the input file;

                iw_s - the (only) line of the file;

                iw_size_s - the maximal capacity of iw_s;

                For the output parser:

                output_file - the output file;

                po_pos - the position in po_line;

                po_line - the current line of the file;

                po_size_line - the maximal capacity of po_line;

                po_s - the currently read element of po_line; also
                  used as temporary buffer;

                po_size_s - the maximal capacity of po_s. ]

  SeeAlso     [ ]

******************************************************************************/
typedef struct Game_SF07_gba_wring_TAG {
  node_ptr formula;       /* The input formula. */
  Game_SF07_gba_ptr gba;  /* The resulting B\"uchi automaton. */
  char* binary_file_name; /* The full path of the Wring binary. */
  char* input_file_name;  /* The full path of the file for the input
                             to Wring. */
  char* output_file_name; /* The full path of the file for the output
                             of Wring. */

  /* For the input writer. */
  FILE* input_file;       /* The input file. */
  char* iw_s;             /* The (only) line of the file. */
  int iw_size_s;          /* The maximal capacity of iw_s. */

  /* For the output parser. */
  FILE* output_file;      /* The output file. */
  int po_pos;             /* The position in po_line. */
  char* po_line;          /* The current line of the file. */
  int po_size_line;       /* The maximal capacity of po_line. */
  char* po_s;             /* The currently read element of
                             po_line. Also used as temporary
                             buffer. */
  int po_size_s;          /* The maximal capacity of po_s. */
} Game_SF07_gba_wring;

/*---------------------------------------------------------------------------*/
/* Variable declarations                                                     */
/*---------------------------------------------------------------------------*/
EXTERN FILE* nusmv_stdout;
EXTERN FILE* nusmv_stderr;

/*---------------------------------------------------------------------------*/
/* Constants declarations                                                    */
/*---------------------------------------------------------------------------*/

/**Constant********************************************************************

  Synopsis    [ Tokens for the parser. ]

  Description [ ]

  SeeAlso     [ ]

******************************************************************************/
#define GAME_SF07_GBA_WRING_TOKEN_DASHES \
"----------------------------------------------------------------------"
#define GAME_SF07_GBA_WRING_TOKEN_STATES "States"
#define GAME_SF07_GBA_WRING_TOKEN_ARCS "Arcs"
#define GAME_SF07_GBA_WRING_TOKEN_FAIRSETS "Fair Sets"
#define GAME_SF07_GBA_WRING_TOKEN_END "End"
#define GAME_SF07_GBA_WRING_TOKEN_LABEL "label"
#define GAME_SF07_GBA_WRING_TOKEN_COLON ":"
#define GAME_SF07_GBA_WRING_TOKEN_LCB "{"
#define GAME_SF07_GBA_WRING_TOKEN_RCB "}"
#define GAME_SF07_GBA_WRING_TOKEN_COMMA ","
#define GAME_SF07_GBA_WRING_TOKEN_ARROW "->"
#define GAME_SF07_GBA_WRING_TOKEN_STATS "Stats"
#define GAME_SF07_GBA_WRING_TOKEN_CPUTIME "CPU time"

/**Constant********************************************************************

  Synopsis    [ Starting size for dynamically enlarged string buffers. ]

  Description [ Must be > 0. ]

  SeeAlso     [ ]

******************************************************************************/
#define GAME_SF07_GBA_WRING_MIN_SIZE_STRING_BUFFERS 81

/**Constant********************************************************************

  Synopsis    [ String of all characters allowed in a formula. ]

  Description [ See LTL.pm. Listed here in ASCII table order. ]

  SeeAlso     [ ]

******************************************************************************/
#define GAME_SF07_GBA_WRING_ALLOWED_CHARS_FORMULA \
"\t !()*+-0123456789<=>ABCDEFGHIJKLMNOPQRSTUVWXYZ^_abcdefghijklmnopqrstuvwxyz"

/**Constant********************************************************************

  Synopsis    [ String of all characters allowed in an atomic
                proposition. ]

  Description [ See LTL.pm: [0-9A-Z_a-z]. Listed here in ASCII table order. ]

  SeeAlso     [ ]

******************************************************************************/
#define GAME_SF07_GBA_WRING_ALLOWED_CHARS_AP \
"0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ_abcdefghijklmnopqrstuvwxyz"

/**Constant********************************************************************

  Synopsis    [ String of all characters allowed in a NuSMV identifier. ]

  Description [ See user manual: [#$\-0-9A-Z_a-z]. Listed here in
                ASCII table order. ]

  SeeAlso     [ ]

******************************************************************************/
#define GAME_SF07_GBA_NUSMV_ALLOWED_CHARS_ID_FIRST \
"ABCDEFGHIJKLMNOPQRSTUVWXYZ_abcdefghijklmnopqrstuvwxyz"
#define GAME_SF07_GBA_NUSMV_ALLOWED_CHARS_ID_AFTERFIRST \
"#$-0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ_abcdefghijklmnopqrstuvwxyz"

/**Constant********************************************************************

  Synopsis    [ File names of last resort to hold the input to and output from
                Wring. ]

  Description [ See Game_SF07_gba_wring_set_{input,output}_file_name for
                details. ]

  SeeAlso     [ ]

******************************************************************************/
#define DEFAULT_GAME_SF07_GBA_WRING_INPUT_FILE_NAME \
"/tmp/tmp.ltl2aut.in"
#define DEFAULT_GAME_SF07_GBA_WRING_OUTPUT_FILE_NAME \
"/tmp/tmp.ltl2aut.out"

/*---------------------------------------------------------------------------*/
/* Macro declarations                                                        */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Static function prototypes                                                */
/*---------------------------------------------------------------------------*/

static int game_sf07_gba_wring_get_next_line
ARGS((Game_SF07_gba_wring_ptr self));

static int game_sf07_gba_wring_read_token ARGS((Game_SF07_gba_wring_ptr self,
                                                const char* token));

static int game_sf07_gba_wring_read_endofline
ARGS((Game_SF07_gba_wring_ptr self));

static int game_sf07_gba_wring_read_whitespaces
ARGS((Game_SF07_gba_wring_ptr self));

static int game_sf07_gba_wring_read_formula
ARGS((Game_SF07_gba_wring_ptr self));

static int game_sf07_gba_wring_read_state_id
ARGS((Game_SF07_gba_wring_ptr self));

static int game_sf07_gba_wring_read_literal
ARGS((Game_SF07_gba_wring_ptr self));

static void game_sf07_gba_wring_ensure_size_iw_s
ARGS((Game_SF07_gba_wring_ptr self, unsigned int size));

static void game_sf07_gba_wring_ensure_size_po_line
ARGS((Game_SF07_gba_wring_ptr self, unsigned int size));

static void game_sf07_gba_wring_ensure_size_po_s
ARGS((Game_SF07_gba_wring_ptr self, unsigned int size));

static void game_sf07_gba_wring_clear_po_s
ARGS((Game_SF07_gba_wring_ptr self));

static void game_sf07_gba_wring_write_input_file_rec
ARGS((NuSMVEnv_ptr env,Game_SF07_gba_wring_ptr self, node_ptr curr));

static void game_sf07_gba_wring_wif_rec_un_op
ARGS((NuSMVEnv_ptr env,Game_SF07_gba_wring_ptr self, char* op, node_ptr car));

static void game_sf07_gba_wring_wif_rec_bin_op
ARGS((NuSMVEnv_ptr env,Game_SF07_gba_wring_ptr self, char* op, node_ptr car, node_ptr cdr));

static void game_sf07_gba_wring_wif_rec_nodeptr
ARGS((NuSMVEnv_ptr env,Game_SF07_gba_wring_ptr self, node_ptr node, boolean delimiters));

static void game_sf07_gba_wring_wif_rec_nodeptr_type
ARGS((Game_SF07_gba_wring_ptr self, short int type));

static void game_sf07_gba_wring_wif_rec_id
ARGS((Game_SF07_gba_wring_ptr self, char* id));

static int game_sf07_gba_wring_varnamestring2nodeptr
ARGS((NuSMVEnv_ptr env, char* s, boolean delimiters, int* pos, node_ptr* literal));

/*---------------------------------------------------------------------------*/
/* Definition of exported functions                                          */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [ Batch function to translate formula into a B\"uchi
                automaton. ]

  Description [ Exports the functionality of this interface and
                supposed to be used by clients. Caller keeps ownership
                of formula (it is treated as a shared
                node_ptr). Caller obtains ownership of returned
                automaton. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
Game_SF07_gba_ptr Game_SF07_gba_wring_ltl2gba(node_ptr formula)
{
  Game_SF07_gba_ptr res;
  Game_SF07_gba_wring_ptr cls;
  int status;

  nusmv_assert(formula != Nil);

  cls = Game_SF07_gba_wring_create();
  Game_SF07_gba_wring_set_formula(cls, formula);
  Game_SF07_gba_wring_set_binary_file_name(cls, NULL);
  Game_SF07_gba_wring_set_input_file_name(cls, NULL);
  Game_SF07_gba_wring_set_output_file_name(cls, NULL);
  Game_SF07_gba_wring_write_input_file(cls);
  status = Game_SF07_gba_wring_execute(cls);
  if (status == 0) {
    Game_SF07_gba_wring_parse_output_file(cls);
    res = Game_SF07_gba_wring_get_gba(cls);
  } else {
    res = GAME_SF07_GBA(NULL);
  }
  Game_SF07_gba_wring_destroy(cls);

  return res;
}

/**Function********************************************************************

  Synopsis    [ Constructor. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ Game_SF07_gba_wring_destroy ]

******************************************************************************/
Game_SF07_gba_wring_ptr Game_SF07_gba_wring_create()
{
  Game_SF07_gba_wring_ptr res;

  res = ALLOC(Game_SF07_gba_wring, 1);
  nusmv_assert(res != GAME_SF07_GBA_WRING(NULL)); /* Can't use macros yet. */

  res->formula = Nil;
  res->gba = GAME_SF07_GBA(NULL);
  res->binary_file_name = (char*) NULL;
  res->input_file_name = (char*) NULL;
  res->input_file = (FILE*) NULL;
  res->iw_s = (char*) NULL;
  res->iw_size_s = 0;
  res->output_file_name = (char*) NULL;
  res->output_file = (FILE*) NULL;
  res->po_pos = 0;
  res->po_line = (char*) NULL;
  res->po_size_line = 0;
  res->po_s = (char*) NULL;
  res->po_size_s = 0;

  return res;
}

/**Function********************************************************************

  Synopsis    [ Destructor. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ Game_SF07_gba_wring_create ]

******************************************************************************/
void Game_SF07_gba_wring_destroy(Game_SF07_gba_wring_ptr self)
{
  GAME_SF07_GBA_WRING_CHECK_INSTANCE(self);

  /* Don't destroy formula: node_ptr are shared. */
  /* Don't destroy gba: handed over to caller. */
  if (self->binary_file_name != (char*) NULL) {
    FREE(self->binary_file_name);
  }
  /* Don't close input_file: supposed to be closed already. */
  if (self->input_file_name != (char*) NULL) {
    /* Try to remove input file if required. */
    if ((!opt_game_sf07_gba_wring_input_keep(OptsHandler_create())) &&
        remove(self->input_file_name) == -1) {
      fprintf(nusmv_stderr,
              "Warning: error deleting file %s (errno = %d).\n",
              self->input_file_name,
              errno);
    }
    FREE(self->input_file_name);
  }
  if (self->iw_s != (char*) NULL) {
    FREE(self->iw_s);
  }
  /* Don't close output_file: supposed to be closed already. */
  if (self->output_file_name != (char*) NULL) {
    /* Try to remove output file if required. */
    if ((!opt_game_sf07_gba_wring_output_keep(OptsHandler_create())) &&
        remove(self->output_file_name) == -1) {
      fprintf(nusmv_stderr,
              "Warning: error deleting file %s (errno = %d).\n",
              self->output_file_name,
              errno);
    }
    FREE(self->output_file_name);
  }
  if (self->po_line != (char*) NULL) {
    FREE(self->po_line);
  }
  if (self->po_s != (char*) NULL) {
    FREE(self->po_s);
  }

  FREE(self);
}

/**Function********************************************************************

  Synopsis    [ Setter for formula. ]

  Description [ Caller keeps ownership of formula (it is treated as a shared
                node_ptr). ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
void Game_SF07_gba_wring_set_formula(Game_SF07_gba_wring_ptr self,
                                     node_ptr formula)
{
  GAME_SF07_GBA_WRING_CHECK_INSTANCE(self);
  nusmv_assert(formula != Nil);

  nusmv_assert(self->formula == Nil);
  self->formula = formula;
}

/**Function********************************************************************

  Synopsis    [ Setter for field binary_file_name. ]

  Description [ Caller keeps ownership of argument
                binary_file_name. If argument binary_file_name is
                NULL, then first the option game_sf07_gba_wring_binary
                is tried and then
                DEFAULT_GAME_SF07_GBA_WRING_BINARY as a last resort.

                Field binary_file_name must not be set yet. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
void Game_SF07_gba_wring_set_binary_file_name(Game_SF07_gba_wring_ptr self,
                                              const char* binary_file_name)
{
  const char* tmp;

  GAME_SF07_GBA_WRING_CHECK_INSTANCE(self);
  nusmv_assert(self->binary_file_name == (char*) NULL);

  if (binary_file_name != (char*) NULL) {
    tmp = binary_file_name;
  } else if (get_game_sf07_gba_wring_binary(OptsHandler_create()) !=
             NULL) {
    tmp = get_game_sf07_gba_wring_binary(OptsHandler_create());
  } else {
    fprintf(nusmv_stderr,
            "Warning: option game_sf07_gba_wring_binary was NULL, reverting "
            "to default %s.\n",
            DEFAULT_GAME_SF07_GBA_WRING_BINARY);
    tmp = DEFAULT_GAME_SF07_GBA_WRING_BINARY;
  }
  self->binary_file_name = ALLOC(char, strlen(tmp) + 1);
  nusmv_assert(self->binary_file_name);
  strcpy(self->binary_file_name, tmp);
}

/**Function********************************************************************

  Synopsis    [ Setter for field input_file_name. ]

  Description [ Caller keeps ownership of argument input_file_name. If
                argument input_file_name is NULL, then first an
                attempt is made to construct a random input file name
                from options game_sf07_gba_wring_input_dir and -templ
                or default values; if that fails, then,
                DEFAULT_GAME_SF07_GBA_WRING_INPUT_FILE_NAME is used as
                a last resort.

                Field input_file_name must not be set yet. ]

  SideEffects []

  SeeAlso     []

******************************************************************************/
void Game_SF07_gba_wring_set_input_file_name(Game_SF07_gba_wring_ptr self,
                                             const char* input_file_name)
{
  GAME_SF07_GBA_WRING_CHECK_INSTANCE(self);
  nusmv_assert(self->input_file_name == (char*) NULL);

  if (input_file_name != (char*) NULL) {
    self->input_file_name = ALLOC(char, strlen(input_file_name) + 1);
    nusmv_assert(self->input_file_name != (char*) NULL);
    strcpy(self->input_file_name, input_file_name);
  } else {
    char* input_dir;
    char* input_templ;

    input_dir = get_game_sf07_gba_wring_input_dir(OptsHandler_create());
    /* input_dir may be NULL */
    input_templ =
      get_game_sf07_gba_wring_input_templ(OptsHandler_create());
    if (input_templ == (char*) NULL) {
      fprintf(nusmv_stderr,
              "Warning: option game_sf07_gba_wring_input_templ was NULL, "
              "reverting to default %s.\n",
              DEFAULT_GAME_SF07_GBA_WRING_INPUT_TEMPL);
      input_templ = DEFAULT_GAME_SF07_GBA_WRING_INPUT_TEMPL;
    }
    self->input_file_name =
      Utils_get_temp_filename_in_dir(input_dir, input_templ);
    if (self->input_file_name == (char*) NULL) {
      fprintf(nusmv_stderr,
              "Warning: unable to obtain temporary file name, reverting to "
              "default %s.\n",
              DEFAULT_GAME_SF07_GBA_WRING_INPUT_FILE_NAME);
      self->input_file_name =
        ALLOC(char, strlen(DEFAULT_GAME_SF07_GBA_WRING_INPUT_FILE_NAME) + 1);
      nusmv_assert(self->input_file_name != (char*) NULL);
      strcpy(self->input_file_name,
             DEFAULT_GAME_SF07_GBA_WRING_INPUT_FILE_NAME);
    }
  }
}

/**Function********************************************************************

  Synopsis    [ Setter for field output_file_name. ]

  Description [ Caller keeps ownership of argument
                output_file_name. If argument output_file_name is
                NULL, then first an attempt is made to construct a
                random output file name from options
                game_sf07_gba_wring_output_dir and -templ or default
                values; if that fails, then,
                DEFAULT_GAME_SF07_GBA_WRING_OUTPUT_FILE_NAME is used
                as a last resort.

                Field output_file_name must not be set yet. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
void Game_SF07_gba_wring_set_output_file_name(Game_SF07_gba_wring_ptr self,
                                              const char* output_file_name)
{
  GAME_SF07_GBA_WRING_CHECK_INSTANCE(self);
  nusmv_assert(self->output_file_name == (char*) NULL);

  if (output_file_name != (char*) NULL) {
    self->output_file_name = ALLOC(char, strlen(output_file_name) + 1);
    nusmv_assert(self->output_file_name != (char*) NULL);
    strcpy(self->output_file_name, output_file_name);
  } else {
    char* output_dir;
    char* output_templ;

    output_dir = get_game_sf07_gba_wring_output_dir(OptsHandler_create());
    /* output_dir may be NULL */
    output_templ =
      get_game_sf07_gba_wring_output_templ(OptsHandler_create());
    if (output_templ == (char*) NULL) {
      fprintf(nusmv_stderr,
              "Warning: option game_sf07_gba_wring_output_templ was NULL, "
              "reverting to default %s.\n",
              DEFAULT_GAME_SF07_GBA_WRING_OUTPUT_TEMPL);
      output_templ = DEFAULT_GAME_SF07_GBA_WRING_OUTPUT_TEMPL;
    }
    self->output_file_name =
      Utils_get_temp_filename_in_dir(output_dir, output_templ);
    if (self->output_file_name == (char*) NULL) {
      fprintf(nusmv_stderr,
              "Warning: unable to obtain temporary file name, reverting to "
              "default %s.\n",
              DEFAULT_GAME_SF07_GBA_WRING_OUTPUT_FILE_NAME);
      self->output_file_name =
        ALLOC(char, strlen(DEFAULT_GAME_SF07_GBA_WRING_OUTPUT_FILE_NAME) + 1);
      nusmv_assert(self->output_file_name != (char*) NULL);
      strcpy(self->output_file_name,
             DEFAULT_GAME_SF07_GBA_WRING_OUTPUT_FILE_NAME);
    }
  }
}

/**Function********************************************************************

  Synopsis    [ Getter for gba. ]

  Description [ self keeps ownership of the returned gba. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
Game_SF07_gba_ptr Game_SF07_gba_wring_get_gba(Game_SF07_gba_wring_ptr self)
{
  GAME_SF07_GBA_WRING_CHECK_INSTANCE(self);

  return self->gba;
}

/**Function********************************************************************

  Synopsis    [ Translates a NuSMV LTL formula into Wring syntax and
                writes it to the input file. ]

  Description [ The formula is given by field formula, the input file
                name is given by field input_file_name.

                NuSMV LTL formulas are translated into Wring LTL formulas as
                follows (see LTL.pm):

                NuSMV         Wring
                ========================
                TRUE/1        TRUE
                FALSE/0       FALSE
                p             p=1
                !             !
                |             +
                &             *
                xor           ^
                xnor          <->
                ->            ->
                <->           <->
                X             X
                F             F
                G             G
                U             U
                V             R

                NuSMV variable names are escaped as follows (as
                suggested by L. Darmawan for TSPASS):

                NuSMV         Wring
                ========================
                $             ZD, D for Dollar
                #             ZK, K for Kres
                -             ZM, M for Minus
                Z             ZZ, Z for Z

                Moreover, ZL and ZR are used as left and right delimiters.

                Currently handling of non-Boolean atoms is restricted
                to =0,=1. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
void Game_SF07_gba_wring_write_input_file(Game_SF07_gba_wring_ptr self)
{
  GAME_SF07_GBA_WRING_CHECK_INSTANCE(self);
  nusmv_assert(self->formula != Nil);
  nusmv_assert(self->input_file_name != (char*) NULL);
  nusmv_assert(self->gba == GAME_SF07_GBA(NULL));

  const NuSMVEnv_ptr env = EnvObject_get_environment(ENV_OBJECT(self->gba));
  const ErrorMgr_ptr errmgr = ERROR_MGR(NuSMVEnv_get_value(env, ENV_ERROR_MANAGER));

  /* Write translated formula into self->iw_s. */
  game_sf07_gba_wring_ensure_size_iw_s(self,
                                   GAME_SF07_GBA_WRING_MIN_SIZE_STRING_BUFFERS);
  self->iw_s[0] = '\0';
  game_sf07_gba_wring_write_input_file_rec(env,self, self->formula);
  game_sf07_gba_wring_ensure_size_iw_s(self, strlen(self->iw_s) + 2);
  strcat(self->iw_s, ";");

  /* Write self->iw_s to self->input_file. */
  self->input_file = fopen(self->input_file_name, "w");
  if (self->input_file == (FILE*) NULL) {
    fprintf(nusmv_stderr,
            "Error opening file %s for writing (errno = %d).\n",
            self->input_file_name,
            errno);
    ErrorMgr_nusmv_exit(errmgr,1);
  }
  fprintf(self->input_file, "%s\n", self->iw_s);
  if (fclose(self->input_file) != 0) {
    fprintf(nusmv_stderr,
            "Error closing file %s (errno = %d).\n",
            self->input_file_name,
            errno);
    ErrorMgr_nusmv_exit(errmgr,1);
  }
}

/**Function********************************************************************

  Synopsis    [ Executes Wring. ]

  Description [ Input file is given by field input_file_name, output
                by field output_field_name. Binary is in
                binary_file_name. If the version of Wring has option
                cc to degeneralized the resulting automaton (as
                specified in option game_sf07_gba_wring_has_cc), then
                it is used.

                Returns 1 on error, 0 otherwise. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
int Game_SF07_gba_wring_execute(Game_SF07_gba_wring_ptr self)
{
  int status;
  char* cmdline;
  unsigned int len_cmdline;

  GAME_SF07_GBA_WRING_CHECK_INSTANCE(self);
  nusmv_assert(self->binary_file_name != (char*) NULL);
  nusmv_assert(self->input_file_name != (char*) NULL);
  nusmv_assert(self->output_file_name != (char*) NULL);
  nusmv_assert(self->gba == GAME_SF07_GBA(NULL));

  /* Build command line. */
  {
    Slist_ptr args;
    Siter a_iter;

    /* Remarks: Slist is a stack, hence push in reverse order. */
    args = Slist_create();
    len_cmdline = 1; /* The trailing '\0'. */
    Slist_push(args, (void*) self->output_file_name);
    len_cmdline += strlen(self->output_file_name);
    Slist_push(args, (void*) " >");
    len_cmdline += strlen(" >");
    Slist_push(args, (void*) self->input_file_name);
    len_cmdline += strlen(self->input_file_name);
    Slist_push(args, (void*) " -ltl ");
    len_cmdline += strlen(" -ltl ");
    if (opt_game_sf07_gba_wring_has_cc(OptsHandler_create())) {
      Slist_push(args, (void*) " -cc");
      len_cmdline += strlen(" -cc");
    }
    Slist_push(args, (void*) self->binary_file_name);
    len_cmdline += strlen(self->binary_file_name);

    cmdline = ALLOC(char, len_cmdline);
    nusmv_assert(cmdline != (char*) NULL);
    cmdline[0] = '\0';

    a_iter = Slist_first(args);
    while (!Siter_is_end(a_iter)) {
      strcat(cmdline, (char*) Siter_element(a_iter));
      a_iter = Siter_next(a_iter);
    }

    Slist_destroy(args);
  }

  if (opt_verbose_level_ge(OptsHandler_create(), 3)) {
    fprintf(nusmv_stderr, "Executing %s\n", cmdline);
  }
  status = system(cmdline);
  if (opt_verbose_level_ge(OptsHandler_create(), 3)) {
    fprintf(nusmv_stderr,
            "Done executing %s. Return value: %d.\n",
            cmdline,
            status);
  }
  if (status != 0) {
    fprintf(nusmv_stderr,
            "Error executing %s on %s.\n",
            self->binary_file_name,
            self->input_file_name);
    status = 1;
    /* Don't exit here b/c this could be due to user specifying wrong
       path to binary. */
  } else {
    status = 0;
  }

  FREE(cmdline);

  return status;
}

/**Function********************************************************************

  Synopsis    [ Parses Wring output file and generates corresponding
                B\"uchi automaton. ]

  Description [ Output file name is given by field output_file_name,
                the automaton is stored in field gba. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
void Game_SF07_gba_wring_parse_output_file(Game_SF07_gba_wring_ptr self)
{
  hash_ptr state_id_2_state; /* Maps state_ids (string_ptrs) to states. */
  int res;                   /* Signals success (== 0) or failure. */

  GAME_SF07_GBA_WRING_CHECK_INSTANCE(self);
  nusmv_assert(self->output_file_name != (char*) NULL);

  const NuSMVEnv_ptr env = EnvObject_get_environment(ENV_OBJECT(self->gba));
  const ErrorMgr_ptr errmgr = ERROR_MGR(NuSMVEnv_get_value(env, ENV_ERROR_MANAGER));
  const NodeMgr_ptr nodemgr = NODE_MGR(NuSMVEnv_get_value(env, ENV_NODE_MGR));
  const UStringMgr_ptr strings = USTRING_MGR(NuSMVEnv_get_value(env, ENV_STRING_MGR));

  /* Open output file. */
  self->output_file = fopen(self->output_file_name, "r");
  if (self->output_file == (FILE*) NULL) {
    fprintf(nusmv_stderr,
            "Error opening file %s for reading (errno = %d).\n",
            self->output_file_name,
            errno);
    ErrorMgr_nusmv_exit(errmgr,1);
  }

  /* Initialize structues. */
  self->gba = Game_SF07_gba_create(Slist_create(),
                                   Slist_create(),
                                   new_assoc(),
                                   Slist_create());
  state_id_2_state = new_assoc();

  /* One line of dashes. Ignored. */
  res = game_sf07_gba_wring_get_next_line(self);
  if (res != 0) { goto ERROR_UNEXPECTED_EOF; }
  res = game_sf07_gba_wring_read_token(self, GAME_SF07_GBA_WRING_TOKEN_DASHES);
  if (res != 0) { goto ERROR_PARSER; }
  game_sf07_gba_wring_clear_po_s(self);
  res = game_sf07_gba_wring_read_endofline(self);
  if (res != 0) { goto ERROR_PARSER; }
  game_sf07_gba_wring_clear_po_s(self);

  /* The input formula. Ignored. */
  res = game_sf07_gba_wring_get_next_line(self);
  if (res != 0) { goto ERROR_UNEXPECTED_EOF; }
  res = game_sf07_gba_wring_read_formula(self);
  if (res != 0) { goto ERROR_PARSER; }
  game_sf07_gba_wring_clear_po_s(self);
  res = game_sf07_gba_wring_read_endofline(self);
  if (res != 0) { goto ERROR_PARSER; }
  game_sf07_gba_wring_clear_po_s(self);

  /* One line of dashes. Ignored. */
  res = game_sf07_gba_wring_get_next_line(self);
  if (res != 0) { goto ERROR_UNEXPECTED_EOF; }
  res = game_sf07_gba_wring_read_token(self, GAME_SF07_GBA_WRING_TOKEN_DASHES);
  if (res != 0) { goto ERROR_PARSER; }
  game_sf07_gba_wring_clear_po_s(self);
  res = game_sf07_gba_wring_read_endofline(self);
  if (res != 0) { goto ERROR_PARSER; }
  game_sf07_gba_wring_clear_po_s(self);

  /* The simplified formula. Ignored. */
  res = game_sf07_gba_wring_get_next_line(self);
  if (res != 0) { goto ERROR_UNEXPECTED_EOF; }
  res = game_sf07_gba_wring_read_formula(self);
  if (res != 0) { goto ERROR_PARSER; }
  game_sf07_gba_wring_clear_po_s(self);
  res = game_sf07_gba_wring_read_endofline(self);
  if (res != 0) { goto ERROR_PARSER; }
  game_sf07_gba_wring_clear_po_s(self);

  /* The token \"States\". Ignored. */
  res = game_sf07_gba_wring_get_next_line(self);
  if (res != 0) { goto ERROR_UNEXPECTED_EOF; }
  res = game_sf07_gba_wring_read_token(self, GAME_SF07_GBA_WRING_TOKEN_STATES);
  if (res != 0) { goto ERROR_PARSER; }
  game_sf07_gba_wring_clear_po_s(self);
  res = game_sf07_gba_wring_read_endofline(self);
  if (res != 0) { goto ERROR_PARSER; }
  game_sf07_gba_wring_clear_po_s(self);

  /* A sequence of lines of states. Extract ids and labels. */
  {
    res = game_sf07_gba_wring_get_next_line(self);
    if (res != 0) { goto ERROR_UNEXPECTED_EOF; }
    res = game_sf07_gba_wring_read_state_id(self);
    while (res == 0) {
      Game_SF07_gba_state_ptr state;
      string_ptr state_id;
      node_ptr label;

      state_id = UStringMgr_find_string(strings,self->po_s);
      game_sf07_gba_wring_clear_po_s(self);

      res = game_sf07_gba_wring_read_token(self,
                                           GAME_SF07_GBA_WRING_TOKEN_COLON);
      if (res != 0) { goto ERROR_PARSER; }
      game_sf07_gba_wring_clear_po_s(self);

      res = game_sf07_gba_wring_read_whitespaces(self);
      if (res != 0) { goto ERROR_PARSER; }
      game_sf07_gba_wring_clear_po_s(self);

      /* A set of formulas. Ignored. */
      {
        res = game_sf07_gba_wring_read_token(self,
                                             GAME_SF07_GBA_WRING_TOKEN_LCB);
        if (res != 0) { goto ERROR_PARSER; }
        game_sf07_gba_wring_clear_po_s(self);

        res = game_sf07_gba_wring_read_formula(self);
        while (res == 0) {
          game_sf07_gba_wring_clear_po_s(self);
          res = game_sf07_gba_wring_read_token(self,
                                               GAME_SF07_GBA_WRING_TOKEN_COMMA);
          if (res == 0) {
            game_sf07_gba_wring_clear_po_s(self);
            res = game_sf07_gba_wring_read_formula(self);
          }
        }

        res = game_sf07_gba_wring_read_token(self,
                                             GAME_SF07_GBA_WRING_TOKEN_RCB);
        if (res != 0) { goto ERROR_PARSER; }
        game_sf07_gba_wring_clear_po_s(self);
      }

      res = game_sf07_gba_wring_read_whitespaces(self);
      if (res != 0) { goto ERROR_PARSER; }
      game_sf07_gba_wring_clear_po_s(self);

      res = game_sf07_gba_wring_read_token(self,
                                           GAME_SF07_GBA_WRING_TOKEN_LABEL);
      if (res != 0) { goto ERROR_PARSER; }
      game_sf07_gba_wring_clear_po_s(self);

      res = game_sf07_gba_wring_read_token(self,
                                           GAME_SF07_GBA_WRING_TOKEN_COLON);
      if (res != 0) { goto ERROR_PARSER; }
      game_sf07_gba_wring_clear_po_s(self);

      res = game_sf07_gba_wring_read_whitespaces(self);
      if (res != 0) { goto ERROR_PARSER; }
      game_sf07_gba_wring_clear_po_s(self);

      /* A set of literals. Needed. */
      {
        label = find_node(nodemgr,TRUEEXP, Nil, Nil);

        res = game_sf07_gba_wring_read_token(self,
                                             GAME_SF07_GBA_WRING_TOKEN_LCB);
        if (res != 0) { goto ERROR_PARSER; }
        game_sf07_gba_wring_clear_po_s(self);

        res = game_sf07_gba_wring_read_literal(self);
        while (res == 0) {
          /* A single literal. Needed. */
          {
            node_ptr literal;
            boolean negative;
            int pos = 0;
            negative = (self->po_s[strlen(self->po_s) - 1] == '0');
            /* Remove =0/1 part. */
            self->po_s[strlen(self->po_s) - 2] = '\0';
            res = game_sf07_gba_wring_varnamestring2nodeptr(env,self->po_s,
                                                            false,
                                                            &pos,
                                                            &literal);
            if (res != 0) { goto ERROR_PARSER; }
            if (negative) { literal = find_node(nodemgr,NOT, literal, Nil); }
            label = find_node(nodemgr,AND, label, literal);
          }
          game_sf07_gba_wring_clear_po_s(self);

          res = game_sf07_gba_wring_read_token(self,
                                               GAME_SF07_GBA_WRING_TOKEN_COMMA);
          if (res == 0) {
            game_sf07_gba_wring_clear_po_s(self);
            res = game_sf07_gba_wring_read_literal(self);
          }
        }

        res = game_sf07_gba_wring_read_token(self,
                                             GAME_SF07_GBA_WRING_TOKEN_RCB);
        if (res != 0) { goto ERROR_PARSER; }
        game_sf07_gba_wring_clear_po_s(self);
      }

      state = Game_SF07_gba_state_create(state_id,
                                         label,
                                         Slist_create(),
                                         Slist_create());
      Game_SF07_gba_add_state(self->gba, state);
      insert_assoc(state_id_2_state, (node_ptr) state_id, (node_ptr) state);

      res = game_sf07_gba_wring_get_next_line(self);
      if (res != 0) { goto ERROR_UNEXPECTED_EOF; }
      res = game_sf07_gba_wring_read_state_id(self);
    }
  }

  /* The token \"Arcs\". Ignored. */
  res = game_sf07_gba_wring_read_token(self, GAME_SF07_GBA_WRING_TOKEN_ARCS);
  if (res != 0) { goto ERROR_PARSER; }
  game_sf07_gba_wring_clear_po_s(self);
  res = game_sf07_gba_wring_read_endofline(self);
  if (res != 0) { goto ERROR_PARSER; }
  game_sf07_gba_wring_clear_po_s(self);

  /* A sequence of lines of sets of transitions. Needed. */
  {
    res = game_sf07_gba_wring_get_next_line(self);
    if (res != 0) { goto ERROR_UNEXPECTED_EOF; }
    res = game_sf07_gba_wring_read_token(self, GAME_SF07_GBA_WRING_TOKEN_ARROW);
    if (res != 0) {
      res = game_sf07_gba_wring_read_whitespaces(self);
    }
    while (res == 0) {
      boolean initial = false;
      string_ptr source_state_id;
      Game_SF07_gba_state_ptr source_state;

      if (self->po_s[0] == '-') {
        /* Read (past tense) token arrow => saw initial state, needed. */
        initial = true;
        game_sf07_gba_wring_clear_po_s(self);
        res = game_sf07_gba_wring_read_whitespaces(self);
        if (res != 0) { goto ERROR_PARSER; }
      }
      game_sf07_gba_wring_clear_po_s(self);

      /* Source state. Needed. */
      res = game_sf07_gba_wring_read_state_id(self);
      if (res != 0) { goto ERROR_PARSER; }
      source_state_id = UStringMgr_find_string(strings,self->po_s);
      source_state =
        GAME_SF07_GBA_STATE(find_assoc(state_id_2_state,
                                       (node_ptr) source_state_id));
      nusmv_assert((node_ptr) source_state != Nil);
      if (initial) {
        Game_SF07_gba_add_state_to_initial_states(self->gba, source_state);
      }
      game_sf07_gba_wring_clear_po_s(self);

      res = game_sf07_gba_wring_read_whitespaces(self);
      if (res != 0) { goto ERROR_PARSER; }
      game_sf07_gba_wring_clear_po_s(self);

      res = game_sf07_gba_wring_read_token(self,
                                           GAME_SF07_GBA_WRING_TOKEN_ARROW);
      if (res != 0) { goto ERROR_PARSER; }
      game_sf07_gba_wring_clear_po_s(self);

      res = game_sf07_gba_wring_read_whitespaces(self);
      if (res != 0) { goto ERROR_PARSER; }
      game_sf07_gba_wring_clear_po_s(self);

      res = game_sf07_gba_wring_read_token(self, GAME_SF07_GBA_WRING_TOKEN_LCB);
      if (res != 0) { goto ERROR_PARSER; }
      game_sf07_gba_wring_clear_po_s(self);

      res = game_sf07_gba_wring_read_state_id(self);
      while (res == 0) {
        /* Target state of a single transition. Needed. */
        {
          string_ptr target_state_id;
          Game_SF07_gba_state_ptr target_state;
          Game_SF07_gba_transition_ptr transition;

          target_state_id = UStringMgr_find_string(strings,self->po_s);
          target_state =
            GAME_SF07_GBA_STATE(find_assoc(state_id_2_state,
                                           (node_ptr) target_state_id));
          nusmv_assert((node_ptr) target_state != Nil);
          transition =
            Game_SF07_gba_transition_create(source_state, target_state);
          Game_SF07_gba_add_transition(self->gba, transition);
          Game_SF07_gba_state_add_outgoing(source_state, transition);
          Game_SF07_gba_state_add_incoming(target_state, transition);
        }
        game_sf07_gba_wring_clear_po_s(self);
        res = game_sf07_gba_wring_read_token(self,
                                             GAME_SF07_GBA_WRING_TOKEN_COMMA);
        if (res == 0) {
          game_sf07_gba_wring_clear_po_s(self);
          res = game_sf07_gba_wring_read_formula(self);
        }
      }

      res = game_sf07_gba_wring_read_token(self, GAME_SF07_GBA_WRING_TOKEN_RCB);
      if (res != 0) { goto ERROR_PARSER; }
      game_sf07_gba_wring_clear_po_s(self);

      res = game_sf07_gba_wring_get_next_line(self);
      if (res != 0) { goto ERROR_UNEXPECTED_EOF; }
      res = game_sf07_gba_wring_read_token(self,
                                           GAME_SF07_GBA_WRING_TOKEN_ARROW);
      if (res != 0) {
        res = game_sf07_gba_wring_read_whitespaces(self);
      }
    }
  }

  /* The token \"Fair Sets\". Ignored. */
  res = game_sf07_gba_wring_read_token(self, GAME_SF07_GBA_WRING_TOKEN_FAIRSETS);
  if (res != 0) { goto ERROR_PARSER; }
  game_sf07_gba_wring_clear_po_s(self);
  res = game_sf07_gba_wring_read_endofline(self);
  if (res != 0) { goto ERROR_PARSER; }
  game_sf07_gba_wring_clear_po_s(self);

  /* A sequence of lines of sets of fair states. Needed. */
  {
    res = game_sf07_gba_wring_get_next_line(self);
    if (res != 0) { goto ERROR_UNEXPECTED_EOF; }
    res = game_sf07_gba_wring_read_token(self, GAME_SF07_GBA_WRING_TOKEN_LCB);
    while (res == 0) {
      hash_ptr fairness_constraint;

      fairness_constraint = new_assoc();
      Game_SF07_gba_add_fairness_constraint(self->gba, fairness_constraint);
      game_sf07_gba_wring_clear_po_s(self);

      res = game_sf07_gba_wring_read_state_id(self);
      while (res == 0) {
        /* A single fair state. Needed. */
        {
          string_ptr fair_state_id;
          Game_SF07_gba_state_ptr fair_state;

          fair_state_id = UStringMgr_find_string(strings,self->po_s);
          fair_state =
            GAME_SF07_GBA_STATE(find_assoc(state_id_2_state,
                                           (node_ptr) fair_state_id));
          nusmv_assert((node_ptr) fair_state != Nil);
          Game_SF07_gba_add_state_to_fairness_constraint(self->gba,
                                                         fairness_constraint,
                                                         fair_state);
        }
        game_sf07_gba_wring_clear_po_s(self);

        res = game_sf07_gba_wring_read_token(self,
                                             GAME_SF07_GBA_WRING_TOKEN_COMMA);
        if (res == 0) {
          game_sf07_gba_wring_clear_po_s(self);
          res = game_sf07_gba_wring_read_formula(self);
        }
      }

      res = game_sf07_gba_wring_read_token(self, GAME_SF07_GBA_WRING_TOKEN_RCB);
      if (res != 0) { goto ERROR_PARSER; }
      game_sf07_gba_wring_clear_po_s(self);

      res = game_sf07_gba_wring_get_next_line(self);
      if (res != 0) { goto ERROR_UNEXPECTED_EOF; }
      res = game_sf07_gba_wring_read_token(self, GAME_SF07_GBA_WRING_TOKEN_LCB);
    }
  }

  /* The token \"End\". Ignored. */
  res = game_sf07_gba_wring_read_token(self, GAME_SF07_GBA_WRING_TOKEN_END);
  if (res != 0) { goto ERROR_PARSER; }
  game_sf07_gba_wring_clear_po_s(self);
  res = game_sf07_gba_wring_read_endofline(self);
  if (res != 0) { goto ERROR_PARSER; }
  game_sf07_gba_wring_clear_po_s(self);

  /* The token \"Stats\". And we ignore the remainder of that line. Ignored. */
  res = game_sf07_gba_wring_get_next_line(self);
  if (res != 0) { goto ERROR_UNEXPECTED_EOF; }
  res = game_sf07_gba_wring_read_token(self, GAME_SF07_GBA_WRING_TOKEN_STATS);
  if (res != 0) { goto ERROR_PARSER; }
  game_sf07_gba_wring_clear_po_s(self);

  /* The token \"CPU Time\". And we ignore the remainder of that
     line. Ignored. */
  res = game_sf07_gba_wring_get_next_line(self);
  if (res != 0) { goto ERROR_UNEXPECTED_EOF; }
  res = game_sf07_gba_wring_read_token(self, GAME_SF07_GBA_WRING_TOKEN_CPUTIME);
  if (res != 0) { goto ERROR_PARSER; }
  game_sf07_gba_wring_clear_po_s(self);

  /* Make sure we have reached the end of file. Ignored. */
  res = game_sf07_gba_wring_get_next_line(self);
  if (res == 0) { res = 1; goto ERROR_EXPECTED_EOF; }
  res = 0;

  /* Normal exit. */
  if (self->po_line != (char*) NULL) {
    FREE(self->po_line);
    self->po_line = (char*) NULL;
    self->po_size_line = 0;
  }
  if (self->po_s != (char*) NULL) {
    FREE(self->po_s);
    self->po_s = (char*) NULL;
    self->po_size_s = 0;
  }
  if (fclose(self->output_file) != 0) {
    fprintf(nusmv_stderr,
            "Error closing file %s (errno = %d).\n",
            self->output_file_name,
            errno);
    ErrorMgr_nusmv_exit(errmgr,1);
  }
  free_assoc(state_id_2_state);
  return;

  /* Error exits. */
 ERROR_UNEXPECTED_EOF:
  fprintf(nusmv_stderr,
          "Error parsing file %s: unexpected end of file.\n",
          self->output_file_name);
  goto CLEAN_UP_AND_EXIT;

 ERROR_EXPECTED_EOF:
  fprintf(nusmv_stderr,
          "Error parsing file %s: expected end of file.\n",
          self->output_file_name);
  goto CLEAN_UP_AND_EXIT;

 ERROR_PARSER:
  fprintf(nusmv_stderr,
          "Error parsing file %s:\n",
          self->output_file_name);
  fprintf(nusmv_stderr, "%s\n", self->po_line);
  {
    int i;
    for (i = 1; i < self->po_pos; i++) {
      fprintf(nusmv_stderr, " ");
    }
  }
  fprintf(nusmv_stderr, "^\n");
  goto CLEAN_UP_AND_EXIT;

 CLEAN_UP_AND_EXIT:
  if (self->po_line != (char*) NULL) {
    FREE(self->po_line);
    self->po_line = (char*) NULL;
    self->po_size_line = 0;
  }
  if (self->po_s != (char*) NULL) {
    FREE(self->po_s);
    self->po_s = (char*) NULL;
    self->po_size_s = 0;
  }
  if (fclose(self->output_file) != 0) {
    fprintf(nusmv_stderr,
            "Error closing file %s (errno = %d).\n",
            self->output_file_name,
            errno);
    ErrorMgr_nusmv_exit(errmgr,1);
  }
  free_assoc(state_id_2_state);
  ErrorMgr_nusmv_exit(errmgr,1);
}

/*---------------------------------------------------------------------------*/
/* Static function definitions                                               */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [ Reads next line from Wring output. ]

  Description [ File is given by field output_file and is assumed to
                be open and left open. The result is stored in field
                po_line. Field po_s is used as a buffer.

                Returns 1 if eof was hit right at the beginning, 0
                otherwise. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
static int game_sf07_gba_wring_get_next_line(Game_SF07_gba_wring_ptr self)
{
  boolean done;
  boolean first;
  unsigned int len;

  GAME_SF07_GBA_WRING_CHECK_INSTANCE(self);

  self->po_pos = 0;

  /* Note: we (ab-)use self->po_s as a buffer here. */
  game_sf07_gba_wring_ensure_size_po_line(self,
                                   GAME_SF07_GBA_WRING_MIN_SIZE_STRING_BUFFERS);
  self->po_line[0] = '\0';
  game_sf07_gba_wring_ensure_size_po_s(self,
                                   GAME_SF07_GBA_WRING_MIN_SIZE_STRING_BUFFERS);
  self->po_s[0] = '\0';

  /* We read chunks into self->po_s and store the sequence of chunks
     in self->po_line. */
  done = false;
  first = true;
  while (!done) {
    fgets(self->po_s, self->po_size_s, self->output_file);
    if (strlen(self->po_s) > 0) {
      if (!feof(self->output_file) &&
          self->po_s[strlen(self->po_s) - 1] != '\n') {
        game_sf07_gba_wring_ensure_size_po_s(self, self->po_size_s + 1);
        done = false;
      } else {
        done = true;
      }
      len = strlen(self->po_line) + strlen(self->po_s) + 1;
      game_sf07_gba_wring_ensure_size_po_line(self, len);
      strcpy(&(self->po_line[strlen(self->po_line)]), self->po_s);
    } else {
      nusmv_assert(feof(self->output_file));
      if (first) {
        return 1;
      } else {
        done = true;
      }
    }
    first = false;
  }

  /* Clean up. */
  self->po_s[0] = '\0';

  return 0;
}

/**Function********************************************************************

  Synopsis    [ Tests whether argument token is present starting at
                position (field) po_pos in (field) po_line. ]

  Description [ Returns 0 if token is indeed found, increases field
                po_pos by the length of token, and copies token into
                field po_s.

                Returns 1 otherwise.

                Caller keeps ownership of token. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
static int game_sf07_gba_wring_read_token(Game_SF07_gba_wring_ptr self,
                                          const char* token)
{
  GAME_SF07_GBA_WRING_CHECK_INSTANCE(self);
  nusmv_assert(token != (char*) NULL);
  nusmv_assert((self->po_size_s > 0) && (strlen(self->po_s) == 0));

  if ((self->po_pos < strlen(self->po_line)) &&
      (strncmp(&(self->po_line[self->po_pos]), token, strlen(token)) == 0)) {
    game_sf07_gba_wring_ensure_size_po_s(self, strlen(token) + 1);
    strcpy(self->po_s, token);
    self->po_pos += strlen(token);
    return 0;
  } else {
    return 1;
  }
}

/**Function********************************************************************

  Synopsis    [ Tests whether an end of line is present starting at
                position (field) po_pos in (field) po_line. ]

  Description [ Reads either "\n" or "\r\n", copies that into field
                po_s, and increases field po_pos correspondingly.

                Returns 0 if the sequence was non-empty, 1 otherwise. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
static int game_sf07_gba_wring_read_endofline(Game_SF07_gba_wring_ptr self)
{
  GAME_SF07_GBA_WRING_CHECK_INSTANCE(self);
  nusmv_assert((self->po_size_s > 0) && (self->po_s[0] == '\0'));

  if (self->po_pos < strlen(self->po_line)) {
    if (strncmp(&(self->po_line[self->po_pos]), "\n", 1) == 0) {
      game_sf07_gba_wring_ensure_size_po_s(self, 2);
      strcpy(self->po_s, "\n");
      self->po_pos += 1;
      return 0;
    } else if (strncmp(&(self->po_line[self->po_pos]), "\r\n", 2) == 0) {
      game_sf07_gba_wring_ensure_size_po_s(self, 3);
      strcpy(self->po_s, "\r\n");
      self->po_pos += 2;
      return 0;
    } else {
      return 1;
    }
  } else {
    return 1;
  }
}

/**Function********************************************************************

  Synopsis    [ Tests whether a non-empty sequence of tabs and spaces is
                present starting at position (field) po_pos in (field)
                po_line. ]

  Description [ Reads maximal non-empty sequence of tabs and spaces,
                copies that sequence into field po_s, and increases
                field po_pos correspondingly.

                Returns 0 if the sequence was non-empty, 1 otherwise. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
static int game_sf07_gba_wring_read_whitespaces(Game_SF07_gba_wring_ptr self)
{
  unsigned int count;

  GAME_SF07_GBA_WRING_CHECK_INSTANCE(self);
  nusmv_assert((self->po_size_s > 0) && (self->po_s[0] == '\0'));

  count = 0;
  if (self->po_pos < strlen(self->po_line)) {
    count = strspn(&(self->po_line[self->po_pos]), " \t");
    game_sf07_gba_wring_ensure_size_po_s(self, count + 1);
    strncat(self->po_s, &(self->po_line[self->po_pos]), count);
    self->po_pos += count;
  }

  if (count > 0) {
    return 0;
  } else {
    return 1;
  }
}

/**Function********************************************************************

  Synopsis    [ Tests whether a non-empty sequence of characters allowed
                in a formula is present starting at position (field)
                po_pos in (field) po_line. ]

  Description [ Reads non-empty maximal sequence of characters allowed
                in a formula (see LTL.pm), copies that sequence into
                field po_s, and increases field po_pos
                correspondingly.

                Returns 0 if the sequence was non-empty, 1 otherwise. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
static int game_sf07_gba_wring_read_formula(Game_SF07_gba_wring_ptr self)
{
  unsigned int count;

  GAME_SF07_GBA_WRING_CHECK_INSTANCE(self);
  nusmv_assert((self->po_size_s > 0) && (self->po_s[0] == '\0'));

  count = 0;
  if (self->po_pos < strlen(self->po_line)) {
    count = strspn(&(self->po_line[self->po_pos]),
                   GAME_SF07_GBA_WRING_ALLOWED_CHARS_FORMULA);
    game_sf07_gba_wring_ensure_size_po_s(self, count + 1);
    strncat(self->po_s, &(self->po_line[self->po_pos]), count);
    self->po_pos += count;
  }

  if (count > 0) {
    return 0;
  } else {
    return 1;
  }
}

/**Function********************************************************************

  Synopsis    [ Tests whether a non-empty sequence of characters
                representing a state identifier is present starting at
                position (field) po_pos in (field) po_line. ]

  Description [ Reads a state identifier as an 'n' followed by a
                non-emtpy, maximal sequence of digits + 'F'. Note that
                this could be made tighter by

                - avoiding leading 0s,

                - considering 'F' only when using lily/acacia,

                - using 'n'['0'-'9']+('F'['0'-'9']+)? rather than
                  'n'['0'-'9''F']+.

                Copies the sequence into field po_s, and increases
                field po_pos correspondingly.

                Returns 0 if the sequence was non-empty, 1 otherwise. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
static int game_sf07_gba_wring_read_state_id(Game_SF07_gba_wring_ptr self)
{
  unsigned int count;

  GAME_SF07_GBA_WRING_CHECK_INSTANCE(self);
  nusmv_assert((self->po_size_s > 0) && (self->po_s[0] == '\0'));

  count = 0;
  if (self->po_pos < strlen(self->po_line) &&
      self->po_line[self->po_pos] == 'n') {
    count = strspn(&(self->po_line[self->po_pos + 1]), "0123456789F");
    if (count > 0) {
      game_sf07_gba_wring_ensure_size_po_s(self, count + 2);
      strncat(self->po_s, &(self->po_line[self->po_pos]), count + 1);
      self->po_pos += count + 1;
    }
  }

  if (count > 0) {
    return 0;
  } else {
    return 1;
  }
}

/**Function********************************************************************

  Synopsis    [ Tests whether a non-empty sequence of characters
                representing a literal is present starting at
                position (field) po_pos in (field) po_line. ]

  Description [ Reads a literal as a non-empty maximal sequence of
                [0-9A-Z_a-z] followed by =0 or =1. Undoes character
                escaping on the way.

                Stores the result into field po_s, and increases
                field po_pos correspondingly.

                Returns 0 if the sequence was non-empty, 1 otherwise. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
static int game_sf07_gba_wring_read_literal(Game_SF07_gba_wring_ptr self)
{
  unsigned int count;

  GAME_SF07_GBA_WRING_CHECK_INSTANCE(self);
  nusmv_assert((self->po_size_s > 0) && (self->po_s[0] == '\0'));

  /* Actually read the literal. */
  count = 0;
  if (self->po_pos < strlen(self->po_line)) {
    count = strspn(&(self->po_line[self->po_pos]),
                   GAME_SF07_GBA_WRING_ALLOWED_CHARS_AP);
    /* Note that the if below is safe as self->po_line ends with a '\0'. */
    if (count > 0 &&
        self->po_line[self->po_pos + count] == '=' &&
        (self->po_line[self->po_pos + count + 1] == '0' ||
         self->po_line[self->po_pos + count + 1] == '1')) {
      game_sf07_gba_wring_ensure_size_po_s(self, count + 3);
      strncat(self->po_s, &(self->po_line[self->po_pos]), count + 2);
      self->po_pos += count + 2;
    }
  }

  if (count > 0) {

    /* Undo the character escaping. */
    {
      unsigned int pos_po_s;
      char* cleaned;
      char c;

      cleaned = ALLOC(char, self->po_size_s);
      nusmv_assert(cleaned != (char*) NULL);
      cleaned[0] = '\0';
      pos_po_s = 0;
      while ((c = self->po_s[pos_po_s]) != '\0') {
        if (c == 'Z') {
          pos_po_s++;
          c = self->po_s[pos_po_s];
          switch (c) {
          case 'D':
            strcat(cleaned, "$");
            break;
          case 'K':
            strcat(cleaned, "#");
            break;
          case 'L':
            strcat(cleaned, "ZL"); /* keep delimiter */
            break;
          case 'M':
            strcat(cleaned, "-");
            break;
          case 'R':
            strcat(cleaned, "ZR"); /* keep delimiter */
            break;
          case 'Z':
            strcat(cleaned, "Z");
            break;
          default:
            nusmv_assert(false);
            break;
          }
        } else {
          unsigned int len;

          len = strlen(cleaned);
          cleaned[len] = c;
          cleaned[len+1] = '\0';
        }
        pos_po_s++;
      }
      FREE(self->po_s);
      self->po_s = cleaned;
    }

    return 0;
  } else {
    return 1;
  }
}

/**Function********************************************************************

  Synopsis    [ Makes sure that the size of field iw_s is at least size. ]

  Description [ Does *2,+1 until at least the desired size is reached. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
static void game_sf07_gba_wring_ensure_size_iw_s(Game_SF07_gba_wring_ptr self,
                                                 unsigned int size)
{
  GAME_SF07_GBA_WRING_CHECK_INSTANCE(self);
  nusmv_assert(size > 0);

  while (self->iw_size_s < size) {
    self->iw_size_s = 2 * self->iw_size_s + 1;
    self->iw_s = REALLOC(char, self->iw_s, self->iw_size_s);
    nusmv_assert(self->iw_s != (char*) NULL);
  }
}

/**Function********************************************************************

  Synopsis    [ Makes sure that the size of field po_line is at least size. ]

  Description [ Does *2,+1 until at least the desired size is reached. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
static void game_sf07_gba_wring_ensure_size_po_line(Game_SF07_gba_wring_ptr self,
                                                    unsigned int size)
{
  GAME_SF07_GBA_WRING_CHECK_INSTANCE(self);
  nusmv_assert(size > 0);

  while (self->po_size_line < size) {
    self->po_size_line = 2 * self->po_size_line + 1;
    self->po_line = REALLOC(char, self->po_line, self->po_size_line);
    nusmv_assert(self->po_line != (char*) NULL);
  }
}

/**Function********************************************************************

  Synopsis    [ Makes sure that the size of field po_s is at least size. ]

  Description [ Does *2,+1 until at least the desired size is reached. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
static void game_sf07_gba_wring_ensure_size_po_s(Game_SF07_gba_wring_ptr self,
                                                 unsigned int size)
{
  GAME_SF07_GBA_WRING_CHECK_INSTANCE(self);
  nusmv_assert(size > 0);

  while (self->po_size_s < size) {
    self->po_size_s = 2 * self->po_size_s + 1;
    self->po_s = REALLOC(char, self->po_s, self->po_size_s);
    nusmv_assert(self->po_s != (char*) NULL);
  }
}

/**Function********************************************************************

  Synopsis    [ Sets po_s to the empty string. ]

  Description [ Makes sure the size of po_s is at least the default minimum. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
static void game_sf07_gba_wring_clear_po_s(Game_SF07_gba_wring_ptr self)
{
  GAME_SF07_GBA_WRING_CHECK_INSTANCE(self);

  game_sf07_gba_wring_ensure_size_po_s(self,
                                   GAME_SF07_GBA_WRING_MIN_SIZE_STRING_BUFFERS);
  self->po_s[0] = '\0';
}

/**Function********************************************************************

  Synopsis    [ Recursive implementation of translation of a NuSMV LTL
                formula into Wring syntax. Result is stored in field
                iw_s. ]

  Description [ See Game_SF07_gba_wring_write_input_file. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
static void
game_sf07_gba_wring_write_input_file_rec(NuSMVEnv_ptr env,Game_SF07_gba_wring_ptr self,
                                         node_ptr curr)
{
  int type;

  GAME_SF07_GBA_WRING_CHECK_INSTANCE(self);
  nusmv_assert(curr != Nil);

  type = node_get_type(curr);

  switch (type) {
    /* Boolean constants. */
  case FALSEEXP:
    game_sf07_gba_wring_ensure_size_iw_s(self, strlen(self->iw_s) + 6);
    strcat(self->iw_s, "FALSE");
    break;
  case TRUEEXP:
    game_sf07_gba_wring_ensure_size_iw_s(self, strlen(self->iw_s) + 5);
    strcat(self->iw_s, "TRUE");
    break;
    /* Atomic propositions. */
  case ARRAY:
  case ATOM:
  case BIT:
  case DOT:
  case NUMBER:
    nusmv_assert((type == ARRAY) ||
                 (type == ATOM && cdr(curr) == Nil) ||
                 (type == BIT) ||
                 (type == DOT) ||
                 (type == NUMBER && cdr(curr) == Nil));
    game_sf07_gba_wring_wif_rec_nodeptr(env,self, curr, false);
    game_sf07_gba_wring_ensure_size_iw_s(self, strlen(self->iw_s) + 3);
    strcat(self->iw_s, "=1");
    break;
    /* Boolean operators. */
  case NOT:
    game_sf07_gba_wring_wif_rec_un_op(env,self, "!", car(curr));
    break;
  case OR:
    game_sf07_gba_wring_wif_rec_bin_op(env,self, "+", car(curr), cdr(curr));
    break;
  case AND:
    game_sf07_gba_wring_wif_rec_bin_op(env,self, "*", car(curr), cdr(curr));
    break;
    /* Temporal operators. */
  case OP_NEXT:
    game_sf07_gba_wring_wif_rec_un_op(env,self, "X", car(curr));
    break;
  case OP_FUTURE:
    game_sf07_gba_wring_wif_rec_un_op(env,self, "F", car(curr));
    break;
  case OP_GLOBAL:
    game_sf07_gba_wring_wif_rec_un_op(env,self, "G", car(curr));
    break;
  case UNTIL:
    game_sf07_gba_wring_wif_rec_bin_op(env,self, "U", car(curr), cdr(curr));
    break;
  case RELEASES:
    game_sf07_gba_wring_wif_rec_bin_op(env,self, "R", car(curr), cdr(curr));
    break;
  default:
    fprintf(nusmv_stderr,
            "Error: unexpected operator %d when writing %s.\n",
            type,
            self->input_file_name);
    nusmv_assert(false);
    break;
  }
}

/**Function********************************************************************

  Synopsis    [ Appends a unary subformula to field iw_s and recursively calls
                game_sf07_gba_wring_write_input_file_rec. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
static void game_sf07_gba_wring_wif_rec_un_op(NuSMVEnv_ptr env,
                                              Game_SF07_gba_wring_ptr self,
                                              char* op,
                                              node_ptr car)
{
  GAME_SF07_GBA_WRING_CHECK_INSTANCE(self);
  nusmv_assert(op != (char*) NULL);
  nusmv_assert(car != Nil);

  game_sf07_gba_wring_ensure_size_iw_s(self,
                                       strlen(self->iw_s) + 2 + strlen(op));
  strcat(self->iw_s, op);
  strcat(self->iw_s, "(");
  game_sf07_gba_wring_write_input_file_rec(env,self, car);
  game_sf07_gba_wring_ensure_size_iw_s(self, strlen(self->iw_s) + 2);
  strcat(self->iw_s, ")");
}

/**Function********************************************************************

  Synopsis    [ Appends a binary subformula to field iw_s and recursively calls
                game_sf07_gba_wring_write_input_file_rec. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
static void game_sf07_gba_wring_wif_rec_bin_op(NuSMVEnv_ptr env,
                                               Game_SF07_gba_wring_ptr self,
                                               char* op,
                                               node_ptr car,
                                               node_ptr cdr)
{
  GAME_SF07_GBA_WRING_CHECK_INSTANCE(self);
  nusmv_assert(op != (char*) NULL);
  nusmv_assert(car != Nil);
  nusmv_assert(cdr != Nil);

  game_sf07_gba_wring_ensure_size_iw_s(self, strlen(self->iw_s) + 2);
  strcat(self->iw_s, "(");
  game_sf07_gba_wring_write_input_file_rec(env,self, car);
  game_sf07_gba_wring_ensure_size_iw_s(self,
                                       strlen(self->iw_s) + 3 + strlen(op));
  strcat(self->iw_s, ")");
  strcat(self->iw_s, op);
  strcat(self->iw_s, "(");
  game_sf07_gba_wring_write_input_file_rec(env,self, cdr);
  game_sf07_gba_wring_ensure_size_iw_s(self,
                                       strlen(self->iw_s) + 2);
  strcat(self->iw_s, ")");
}

/**Function********************************************************************

  Synopsis    [ Appends a node_ptr as a string to field iw_s. ]

  Description [ This is designed to turn (possibily hierarchical,
                bit-ted) NuSMV variable names into Wring variable
                names. It accepts a very limited set of node
                types. The output is expected to be parsed by
                game_sf07_gba_wring_varnamestring2nodeptr.

                The encoding is as follows
                - Nil is dumped as is.
                - Other node types are written as "ZL" + type + "ZR" +
                  "ZL" + car + "ZR" + "ZL" + cdr + "ZR". "ZL", "ZR"
                  stand for left and right delimiter, respectively.

                If delimiters is true, then node is wrapped into "ZL",
                "ZR", too. ]

  SideEffects [ ]

  SeeAlso     [ game_sf07_gba_wring_varnamestring2nodeptr ]

******************************************************************************/
static void game_sf07_gba_wring_wif_rec_nodeptr(NuSMVEnv_ptr env,
                                                Game_SF07_gba_wring_ptr self,
                                                node_ptr node,
                                                boolean delimiters)
{

    MasterPrinter_ptr wffprint = MASTER_PRINTER(NuSMVEnv_get_value(env, ENV_WFF_PRINTER));

  GAME_SF07_GBA_WRING_CHECK_INSTANCE(self);

  if (delimiters) {
    game_sf07_gba_wring_ensure_size_iw_s(self, strlen(self->iw_s) + 3);
    strcat(self->iw_s, "ZL");
  }

  if (node == Nil) {
    game_sf07_gba_wring_ensure_size_iw_s(self, strlen(self->iw_s) + 4);
    strcat(self->iw_s, "Nil");
  } else {
    short int type;

    type = node_get_type(node);

    nusmv_assert((type == ARRAY) ||
                 (type == ATOM && cdr(node) == Nil) ||
                 (type == BIT) ||
                 (type == DOT) ||
                 (type == NUMBER && cdr(node) == Nil));

    /* Write type. */
    game_sf07_gba_wring_wif_rec_nodeptr_type(self, type);
    switch (type) {
    case ARRAY:
    case DOT:
      /* Write car. */
      game_sf07_gba_wring_wif_rec_nodeptr(env,self, car(node), true);
      /* Write cdr. */
      game_sf07_gba_wring_wif_rec_nodeptr(env,self, cdr(node), true);
      break;
    case ATOM:
      /* Write car. */
      {
        char* tmp;

        tmp = sprint_node(wffprint,node);
        nusmv_assert(tmp != (char*) NULL);

        game_sf07_gba_wring_ensure_size_iw_s(self, strlen(self->iw_s) + 3);
        strcat(self->iw_s, "ZL");
        game_sf07_gba_wring_wif_rec_id(self, tmp);
        game_sf07_gba_wring_ensure_size_iw_s(self, strlen(self->iw_s) + 3);
        strcat(self->iw_s, "ZR");

        FREE(tmp);
      }
      /* Write cdr. */
      nusmv_assert(cdr(node) == Nil);
      game_sf07_gba_wring_wif_rec_nodeptr(env,self, cdr(node), true);
      break;
    case BIT:
      /* Write car. */
      game_sf07_gba_wring_wif_rec_nodeptr(env,self, car(node), true);
      /* Write cdr. */
      {
        char* tmp;
        int l;

        tmp = ALLOC(char, 100);
        nusmv_assert(tmp != (char*) NULL);
        l = snprintf(tmp, 100, "%d", NODE_TO_INT(cdr(node)));
        nusmv_assert(l < 100);

        game_sf07_gba_wring_ensure_size_iw_s(self, strlen(self->iw_s) + 3);
        strcat(self->iw_s, "ZL");
        game_sf07_gba_wring_ensure_size_iw_s(self, strlen(self->iw_s) + l + 1);
        strcat(self->iw_s, tmp);
        game_sf07_gba_wring_ensure_size_iw_s(self, strlen(self->iw_s) + 3);
        strcat(self->iw_s, "ZR");

        FREE(tmp);
      }
      break;
    case NUMBER:
      /* Write car. */
      {
        char* tmp;
        int l;

        tmp = ALLOC(char, 100);
        nusmv_assert(tmp != (char*) NULL);
        l = snprintf(tmp, 100, "%d", NODE_TO_INT(car(node)));
        nusmv_assert(l < 100);

        game_sf07_gba_wring_ensure_size_iw_s(self, strlen(self->iw_s) + 3);
        strcat(self->iw_s, "ZL");
        game_sf07_gba_wring_ensure_size_iw_s(self, strlen(self->iw_s) + l + 1);
        strcat(self->iw_s, tmp);
        game_sf07_gba_wring_ensure_size_iw_s(self, strlen(self->iw_s) + 3);
        strcat(self->iw_s, "ZR");

        FREE(tmp);
      }
      /* Write cdr. */
      nusmv_assert(cdr(node) == Nil);
      game_sf07_gba_wring_wif_rec_nodeptr(env,self, cdr(node), true);
      break;
    default:
      nusmv_assert(false);
    }
  }

  if (delimiters) {
    game_sf07_gba_wring_ensure_size_iw_s(self, strlen(self->iw_s) + 3);
    strcat(self->iw_s, "ZR");
  }
}

/**Function********************************************************************

  Synopsis    [ Appends a node_ptr type as a string to field iw_s. ]

  Description [ Surrounds type with "ZL" and "ZR" as left and right
                delimiters. Very limited number of types. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
static void
game_sf07_gba_wring_wif_rec_nodeptr_type(Game_SF07_gba_wring_ptr self,
                                         short int type)
{
  GAME_SF07_GBA_WRING_CHECK_INSTANCE(self);

  game_sf07_gba_wring_ensure_size_iw_s(self, strlen(self->iw_s) + 3);
  strcat(self->iw_s, "ZL");
  switch (type) {
  case ARRAY:
    game_sf07_gba_wring_wif_rec_id(self, "ARRAY"); /* slight abuse */
    break;
  case ATOM:
    game_sf07_gba_wring_wif_rec_id(self, "ATOM"); /* slight abuse */
    break;
  case BIT:
    game_sf07_gba_wring_wif_rec_id(self, "BIT"); /* slight abuse */
    break;
  case DOT:
    game_sf07_gba_wring_wif_rec_id(self, "DOT"); /* slight abuse */
    break;
  case NUMBER:
    game_sf07_gba_wring_wif_rec_id(self, "NUMBER"); /* slight abuse */
    break;
  default:
    nusmv_assert(false);
  }
  game_sf07_gba_wring_ensure_size_iw_s(self, strlen(self->iw_s) + 3);
  strcat(self->iw_s, "ZR");
}

/**Function********************************************************************

  Synopsis    [ Appends a NuSMV id to field iw_s. ]

  Description [ The string must me a legal id according to the NuSMV
                user man, i.e., consist only of characters in
                GAME_SF07_GBA_WRING_ALLOWED_CHARS_ID_(AFTER)FIRST.

                [$#-Z] are escaped.

                Abused to write node_ptr types as strings. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
static void game_sf07_gba_wring_wif_rec_id(Game_SF07_gba_wring_ptr self,
                                           char* id)
{
  int pos;

  GAME_SF07_GBA_WRING_CHECK_INSTANCE(self);
  nusmv_assert(id != (char*) NULL);

  pos = 0;
  while (id[pos] != '\0') {
    nusmv_assert((pos == 0 &&
                  strchr(GAME_SF07_GBA_NUSMV_ALLOWED_CHARS_ID_FIRST,
                         id[pos]) !=
                  (char*) NULL) ||
                 (pos > 0 &&
                  strchr(GAME_SF07_GBA_NUSMV_ALLOWED_CHARS_ID_AFTERFIRST,
                         id[pos]) !=
                  (char*) NULL));
    switch (id[pos]) {
    case '$':
      game_sf07_gba_wring_ensure_size_iw_s(self, strlen(self->iw_s) + 3);
      strcat(self->iw_s, "ZD");
      break;
    case '#':
      game_sf07_gba_wring_ensure_size_iw_s(self, strlen(self->iw_s) + 3);
      strcat(self->iw_s, "ZK");
      break;
    case '-':
      game_sf07_gba_wring_ensure_size_iw_s(self, strlen(self->iw_s) + 3);
      strcat(self->iw_s, "ZM");
      break;
    case 'Z':
      game_sf07_gba_wring_ensure_size_iw_s(self, strlen(self->iw_s) + 3);
      strcat(self->iw_s, "ZZ");
      break;
    default:
      {
        int len;
        game_sf07_gba_wring_ensure_size_iw_s(self, strlen(self->iw_s) + 2);
        len = strlen(self->iw_s);
        self->iw_s[len] = id[pos];
        self->iw_s[len+1] = '\0';
        break;
      }
    }
    pos++;
  }
}

/**Function********************************************************************

  Synopsis    [ Takes a (possibly hierarchical, bit-ted) variable name as
                a string and produces the corresponding node_ptr. ]

  Description [ The input s is expected to be produced by
                game_sf07_gba_wring_wif_rec_nodeptr. *pos is initially
                the starting position in s and after the call the
                first character after reading the result.

                If delimiters is true, then the node is expected to be
                wrapped into "ZL", "ZR", too.

                The resulting node_ptr is returned in literal.

                Returns 1 upon error, 0 otherwise. ]

  SideEffects [ ]

  SeeAlso     [ game_sf07_gba_wring_wif_rec_nodeptr ]

******************************************************************************/
static int game_sf07_gba_wring_varnamestring2nodeptr(NuSMVEnv_ptr env,
                                                     char* s,
                                                     boolean delimiters,
                                                     int* pos,
                                                     node_ptr* literal)
{
  node_ptr res;

  const NodeMgr_ptr nodemgr = NODE_MGR(NuSMVEnv_get_value(env, ENV_NODE_MGR));
  const UStringMgr_ptr strings = USTRING_MGR(NuSMVEnv_get_value(env, ENV_STRING_MGR));

  nusmv_assert(s != (char*) NULL);
  nusmv_assert(pos != (int*) NULL);
  nusmv_assert(strlen(s) >= *pos);

  if (delimiters) {
    if (strncmp(&(s[*pos]), "ZL", 2) != 0) {
      goto game_sf07_gba_wring_varnamestring2nodeptr_return_1;
    }
    *pos += 2;
  }

  if (strncmp(&(s[*pos]), "Nil", 3) == 0) {
    *pos += 3;
    res = Nil;
  } else {
    short int type;
    node_ptr lhs, rhs;

    if (strncmp(&(s[*pos]), "ZL", 2) != 0) {
      goto game_sf07_gba_wring_varnamestring2nodeptr_return_1;
    }
    *pos += 2;
    if (strncmp(&(s[*pos]), "ARRAY", 5) == 0) {
      *pos += 5;
      type = ARRAY;
      if (strncmp(&(s[*pos]), "ZR", 2) != 0) {
        goto game_sf07_gba_wring_varnamestring2nodeptr_return_1;
      }
      *pos += 2;
      if (game_sf07_gba_wring_varnamestring2nodeptr(env,s, true, pos, &lhs) != 0) {
        goto game_sf07_gba_wring_varnamestring2nodeptr_return_1;
      }
      if (game_sf07_gba_wring_varnamestring2nodeptr(env,s, true, pos, &rhs) != 0) {
        goto game_sf07_gba_wring_varnamestring2nodeptr_return_1;
      }
    } else if (strncmp(&(s[*pos]), "ATOM", 4) == 0) {
      *pos += 4;
      type = ATOM;
      if (strncmp(&(s[*pos]), "ZR", 2) != 0) {
        goto game_sf07_gba_wring_varnamestring2nodeptr_return_1;
      }
      *pos += 2;
      {
        char* pos_first_zr;

        if (strncmp(&(s[*pos]), "ZL", 2) != 0) {
          goto game_sf07_gba_wring_varnamestring2nodeptr_return_1;
        }
        *pos += 2;

        pos_first_zr = strstr(&(s[*pos]), "ZR");
        if (pos_first_zr == (char*) NULL) {
          goto game_sf07_gba_wring_varnamestring2nodeptr_return_1;
        }

        *pos_first_zr = '\0'; /* simulate shorter s */
        lhs = (node_ptr) UStringMgr_find_string(strings,&(s[*pos]));
        *pos = strlen(s);
        *pos_first_zr = 'Z'; /* restore s */

        if (strncmp(&(s[*pos]), "ZR", 2) != 0) {
          goto game_sf07_gba_wring_varnamestring2nodeptr_return_1;
        }
        *pos += 2;
      }
      if (game_sf07_gba_wring_varnamestring2nodeptr(env,s, true, pos, &rhs) != 0) {
        goto game_sf07_gba_wring_varnamestring2nodeptr_return_1;
      }
      if (rhs != Nil) {
        goto game_sf07_gba_wring_varnamestring2nodeptr_return_1;
      }
    } else if (strncmp(&(s[*pos]), "BIT", 3) == 0) {
      *pos += 3;
      type = BIT;
      if (strncmp(&(s[*pos]), "ZR", 2) != 0) {
        goto game_sf07_gba_wring_varnamestring2nodeptr_return_1;
      }
      *pos += 2;
      if (game_sf07_gba_wring_varnamestring2nodeptr(env,s, true, pos, &lhs) != 0) {
        goto game_sf07_gba_wring_varnamestring2nodeptr_return_1;
      }
      if (lhs == Nil) {
        goto game_sf07_gba_wring_varnamestring2nodeptr_return_1;
      }
      {
        char* pos_first_z;
        int n, i;

        if (strncmp(&(s[*pos]), "ZL", 2) != 0) {
          goto game_sf07_gba_wring_varnamestring2nodeptr_return_1;
        }
        *pos += 2;

        /* No chars in unsigned int, hence just find first Z. */
        pos_first_z = strchr(&(s[*pos]), 'Z');
        if (pos_first_z == (char*) NULL) {
          goto game_sf07_gba_wring_varnamestring2nodeptr_return_1;
        }
        pos_first_z++;
        if (*pos_first_z != 'R') {
          goto game_sf07_gba_wring_varnamestring2nodeptr_return_1;
        }
        pos_first_z--;

        *pos_first_z = '\0'; /* simulate shorter s */
        n = sscanf(&(s[*pos]), "%u", &i);
        if (n != 1) {
          goto game_sf07_gba_wring_varnamestring2nodeptr_return_1;
        }
        *pos = strlen(s);
        *pos_first_z = 'Z'; /* restore s */
        rhs = NODE_FROM_INT(i);

        if (strncmp(&(s[*pos]), "ZR", 2) != 0) {
          goto game_sf07_gba_wring_varnamestring2nodeptr_return_1;
        }
        *pos += 2;
      }
    } else if (strncmp(&(s[*pos]), "DOT", 3) == 0) {
      *pos += 3;
      type = DOT;
      if (strncmp(&(s[*pos]), "ZR", 2) != 0) {
        goto game_sf07_gba_wring_varnamestring2nodeptr_return_1;
      }
      *pos += 2;
      if (game_sf07_gba_wring_varnamestring2nodeptr(env,s, true, pos, &lhs) != 0) {
        goto game_sf07_gba_wring_varnamestring2nodeptr_return_1;
      }
      if (game_sf07_gba_wring_varnamestring2nodeptr(env,s, true, pos, &rhs) != 0) {
        goto game_sf07_gba_wring_varnamestring2nodeptr_return_1;
      }
    } else if (strncmp(&(s[*pos]), "NUMBER", 6) == 0) {
      *pos += 6;
      type = NUMBER;
      if (strncmp(&(s[*pos]), "ZR", 2) != 0) {
        goto game_sf07_gba_wring_varnamestring2nodeptr_return_1;
      }
      *pos += 2;
      {
        char* pos_first_z;
        int n, i;

        if (strncmp(&(s[*pos]), "ZL", 2) != 0) {
          goto game_sf07_gba_wring_varnamestring2nodeptr_return_1;
        }
        *pos += 2;

        /* No chars in unsigned int, hence just find first Z. */
        pos_first_z = strchr(&(s[*pos]), 'Z');
        if (pos_first_z == (char*) NULL) {
          goto game_sf07_gba_wring_varnamestring2nodeptr_return_1;
        }
        pos_first_z++;
        if (*pos_first_z != 'R') {
          goto game_sf07_gba_wring_varnamestring2nodeptr_return_1;
        }
        pos_first_z--;

        *pos_first_z = '\0'; /* simulate shorter s */
        n = sscanf(&(s[*pos]), "%u", &i);
        if (n != 1) {
          goto game_sf07_gba_wring_varnamestring2nodeptr_return_1;
        }
        *pos = strlen(s);
        *pos_first_z = 'Z'; /* restore s */
        lhs = NODE_FROM_INT(i);

        if (strncmp(&(s[*pos]), "ZR", 2) != 0) {
          goto game_sf07_gba_wring_varnamestring2nodeptr_return_1;
        }
        *pos += 2;
      }
      if (game_sf07_gba_wring_varnamestring2nodeptr(env,s, true, pos, &rhs) != 0) {
        goto game_sf07_gba_wring_varnamestring2nodeptr_return_1;
      }
      if (rhs != Nil) {
        goto game_sf07_gba_wring_varnamestring2nodeptr_return_1;
      }
    } else {
      nusmv_assert(false);
    }

    res = find_node(nodemgr,type, lhs, rhs);
  }

  if (delimiters) {
    if (strncmp(&(s[*pos]), "ZR", 2) != 0) {
      goto game_sf07_gba_wring_varnamestring2nodeptr_return_1;
    }
    *pos += 2;
  }

  *literal = res;
  return 0;

 game_sf07_gba_wring_varnamestring2nodeptr_return_1:
  *literal = FAILURE_NODE;
  return 1;
}
