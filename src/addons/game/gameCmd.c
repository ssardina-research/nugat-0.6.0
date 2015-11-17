/**CFile***********************************************************************

  FileName    [ gameCmd.c ]

  PackageName [ game ]

  Synopsis    [ Commands for game. ]

  Description [ This file contains the shell command for game. ]

  SeeAlso     [ cmdCmd.c ]

  Author      [ Andrei Tchaltsev, Viktor Schuppan ]

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
#include "PropGame.h"
#include "PropDbGame.h"

#include "utils/error.h" /* for CATCH(errmgr) */
#include "prop/propPkg.h"
#include "cmd/cmd.h"
#include "cmd/cmdInt.h"
#include "utils/ucmd.h"
#include "utils/utils_io.h"
#include "utils/NodeList.h"
#include "compile/compileInt.h" /* for flattening functions */

/*---------------------------------------------------------------------------*/
static char rcsid[] UTIL_UNUSED = "$Id: gameCmd.c,v 1.1.2.10 2010-02-08 12:25:25 nusmv Exp $";
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Type declarations                                                         */
/*---------------------------------------------------------------------------*/

/**Type************************************************************************

  Synopsis    [ Signature of (some) functions to check game properties. ]

  Description [ ]

  SeeAlso     [ game_invoke_game_command ]

******************************************************************************/
typedef void (*command_function_ptr) (NuSMVEnv_ptr env, PropGame_ptr prop, gameParams_ptr params);

/*---------------------------------------------------------------------------*/
/* Static function prototypes                                                */
/*---------------------------------------------------------------------------*/

/* This section goes earlier in this file as declarations are needed
   for variable declarations below. */

/* Prototypes of the command functions. */

/* Commands that exists also in non-game but are overridden. */
static int CommandGameBuildBooleanModel ARGS((NuSMVEnv_ptr env,int argc, char ** argv));
                                        static int CommandGameBuildFlatModel ARGS((NuSMVEnv_ptr env,int argc, char ** argv));
                                        static int CommandGameBuildModel ARGS((NuSMVEnv_ptr env,int argc, char ** argv));
                                        static int CommandGameCheckProperty ARGS((NuSMVEnv_ptr env,int argc, char** argv));
                                        static int CommandGameEncodeVariables ARGS((NuSMVEnv_ptr env,int argc, char ** argv));
                                        static int CommandGameFlattenHierarchy ARGS((NuSMVEnv_ptr env,int argc, char **argv));
                                        static int CommandGamePrintUsage ARGS((NuSMVEnv_ptr env,int argc, char** argv));
                                        static int CommandGameShowProperty ARGS((NuSMVEnv_ptr env,int argc, char** argv));
                                        static int CommandGameWriteModelFlatBool ARGS((NuSMVEnv_ptr env,int argc, char **argv));
                                        static int CommandGameWriteModelFlat ARGS((NuSMVEnv_ptr env,int argc, char **argv));

/* Commands specific to game. */
                                        static int CommandReadRatFile ARGS((NuSMVEnv_ptr env,int argc, char **argv));
                                        static int CommandCheckReachTargetSpec ARGS((NuSMVEnv_ptr env,int argc, char **argv));
                                        static int CommandCheckReachDeadlockSpec ARGS((NuSMVEnv_ptr env,int argc, char **argv));
                                        static int CommandCheckAvoidTargetSpec ARGS((NuSMVEnv_ptr env,int argc, char **argv));
                                        static int CommandCheckAvoidDeadlockSpec ARGS((NuSMVEnv_ptr env,int argc, char **argv));
                                        static int CommandCheckBuchiGameSpec ARGS((NuSMVEnv_ptr env,int argc, char **argv));
                                        static int CommandCheckLtlGameSpecSF07 ARGS((NuSMVEnv_ptr env,int argc, char **argv));
                                        static int CommandCheckGenReactivitySpec ARGS((NuSMVEnv_ptr env,int argc, char **argv));
                                        static int CommandExtractUnrealizableCore ARGS((NuSMVEnv_ptr env,int argc, char **argv));

/* Prototypes of function to print the command's usage. */

/* Commands that exists also in non-game but are overridden. */
                                        static int UsageGameBuildBooleanModel ARGS((void));
                                        static int UsageGameBuildFlatModel ARGS((void));
                                        static int UsageGameBuildModel ARGS((void));
                                        static int UsageGameCheckProperty ARGS((void));
                                        static int UsageGameEncodeVariables ARGS((void));
                                        static int UsageGameFlattenHierarchy ARGS((void));
                                        static int UsageGamePrintUsage ARGS((void));
                                        static int UsageGameShowProperty ARGS((void));
                                        static int UsageGameWriteModelFlat ARGS((void));
                                        static int UsageGameWriteModelFlatBool ARGS((void));

/* Commands specific to game. */
                                        static int UsageReadRatFile ARGS((void));
                                        static int UsageCheckReachTargetSpec ARGS((void));
                                        static int UsageCheckReachDeadlockSpec ARGS((void));
                                        static int UsageCheckAvoidTargetSpec ARGS((void));
                                        static int UsageCheckAvoidDeadlockSpec ARGS((void));
                                        static int UsageCheckBuchiGameSpec ARGS((void));
                                        static int UsageCheckLtlGameSpecSF07 ARGS((void));
                                        static int UsageCheckGenReactivitySpec ARGS((void));
                                        static int UsageExtractUnrealizableCore ARGS((void));

/* Prototypes of non-command functions. */

                                        static int game_invoke_game_command ARGS((NuSMVEnv_ptr env,
                                                                                  int argc,
                                                                                  char **argv,
                                                                                  PropGame_Type type));
                                        static NodeList_ptr game_cmd_init_commands_list ARGS((CommandDescr_t *commands,
                                                                                              int len));

/*---------------------------------------------------------------------------*/
/* Variable declarations                                                     */
/*---------------------------------------------------------------------------*/
;
/**Variable********************************************************************

  Synopsis    [ These are the generic commands, i.e., those that apply
                equally to game and non-game mode. ]

  Description [ If the second field, command_fp is != NULL, then this
                command is added/removed in Game_init/quit_cmd. ]

  SeeAlso     [ ]

******************************************************************************/
static CommandDescr_t generic_commands[] = {
        {"alias",                (PFI) NULL, 0, false},
        {"clean_bdd_cache",      (PFI) NULL, 0, false},
        {"dynamic_var_ordering", (PFI) NULL, 0, false},
        {"echo",                 (PFI) NULL, 0, false},
        {"get_internal_status",  (PFI) NULL, 0, false},
        /* go is here for now as its implementation uses only calls to
           commands and with options that are appropriately overloaded. In a
           sense that works because its subroutines are virtual functions
           using late binding and no dependent options.*/
        {"go",                   (PFI) NULL, 0, false},
        {"help",                 (PFI) NULL, 0, false},
        {"history",              (PFI) NULL, 0, false},
        {"print_bdd_stats",      (PFI) NULL, 0, false},
        {"print_iwls95options",  (PFI) NULL, 0, false},
        {"print_formula",        (PFI) NULL, 0, false},
        {"quit",                 (PFI) NULL, 0, false},
        {"read_model",           (PFI) NULL, 0, false},
        {"read_rat_file",        CommandReadRatFile, 0, true},
        {"reset",                (PFI) NULL, 0, false},
        {"set",                  (PFI) NULL, 0, false},
        {"set_bdd_parameters",   (PFI) NULL, 0, false},
        {"show_vars",            (PFI) NULL, 0, false},
        {"source",               (PFI) NULL, 0, false},
        {"time",                 (PFI) NULL, 0, false},
        {"unalias",              (PFI) NULL, 0, false},
        {"unset",                (PFI) NULL, 0, false},
        {"usage",                (PFI) NULL, 0, false},
        {"which",                (PFI) NULL, 0, false},
        {"write_order",          (PFI) NULL, 0, false},
        {"_memory_profile",      (PFI) NULL, 0, false},
        {"_show_help",           (PFI) NULL, 0, false}
};

/**Variable********************************************************************

  Synopsis    [ These are the dependent commands, i.e., those that apply,
                but differently, to game and non-game mode. ]

  Description [ ]

  SeeAlso     [ ]

******************************************************************************/
/* Not available as of now
   {"add_property",        CommandAddProperty,            0, true},
*/
/* Conceptually process_model fits here. However, when used with "-i"
   the actual Command[Game]ProcessModel has already been entered
   before possibly executing a mode switch. A solution could be using
   hidden commands or virtual functions, but that seems to clutter up
   the commands, so not doing it for now.
*/
static CommandDescr_t dependent_commands[] = {
        {"build_boolean_model", CommandGameBuildBooleanModel,  0, false},
        {"build_flat_model",    CommandGameBuildFlatModel,     0, false},
        {"build_model",         CommandGameBuildModel,         0, false},
        {"check_property",      CommandGameCheckProperty,      0, true},
        {"encode_variables",    CommandGameEncodeVariables,    0, false},
        {"flatten_hierarchy",   CommandGameFlattenHierarchy,   0, false},
        {"print_usage",         CommandGamePrintUsage,         0, true},
        {"show_property",       CommandGameShowProperty,       0, true},
        {"write_boolean_model", CommandGameWriteModelFlatBool, 0, true},
        {"write_flat_model",    CommandGameWriteModelFlat,     0, true}
};

/**Variable********************************************************************

  Synopsis    [ These are the specific commands, i.e., those that apply
                only in game mode. ]

  Description [ ]

  SeeAlso     [ ]

******************************************************************************/
static CommandDescr_t specific_commands[] = {
        {"check_reach_target",        CommandCheckReachTargetSpec,    0, true},
        {"check_reach_deadlock",      CommandCheckReachDeadlockSpec,  0, true},
        {"check_avoid_target",        CommandCheckAvoidTargetSpec,    0, true},
        {"check_avoid_deadlock",      CommandCheckAvoidDeadlockSpec,  0, true},
        {"check_buchi_game",          CommandCheckBuchiGameSpec,      0, true},
        {"check_ltlgame_sf07",        CommandCheckLtlGameSpecSF07,    0, true},
        {"check_gen_reactivity",      CommandCheckGenReactivitySpec,  0, true},
        {"extract_unrealizable_core", CommandExtractUnrealizableCore, 0, true}
};

/**Variable********************************************************************

  Synopsis    [ These are NodeLists of commands to avoid handing arrays
                around. ]

  Description [ ]

  SeeAlso     [ ]

******************************************************************************/
static NodeList_ptr generic_commands_list = NODE_LIST(NULL);
static NodeList_ptr dependent_commands_list = NODE_LIST(NULL);
static NodeList_ptr specific_commands_list = NODE_LIST(NULL);

/*---------------------------------------------------------------------------*/
/* Definition of exported functions                                          */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [ Initializer for file. ]

  Description [ Fills NodeLists of commands. ]

  SideEffects [ ]

  SeeAlso     [ Game_Init, Game_init_cmd ]

******************************************************************************/
void Game_init_cmd()
{
    nusmv_assert(generic_commands_list == NODE_LIST(NULL));
    nusmv_assert(dependent_commands_list == NODE_LIST(NULL));
    nusmv_assert(specific_commands_list == NODE_LIST(NULL));

    generic_commands_list =
            game_cmd_init_commands_list(generic_commands,
                                        (sizeof(generic_commands) /
                                         sizeof(generic_commands[0])));
    dependent_commands_list =
            game_cmd_init_commands_list(dependent_commands,
                                        (sizeof(dependent_commands) /
                                         sizeof(dependent_commands[0])));
    specific_commands_list =
            game_cmd_init_commands_list(specific_commands,
                                        (sizeof(specific_commands) /
                                         sizeof(specific_commands[0])));
}

/**Function********************************************************************

  Synopsis    [ Deinitializer for file. ]

  Description [ Frees NodeLists of commands. ]

  SideEffects [ ]

  SeeAlso     [ Game_Quit, Game_init_cmd ]

******************************************************************************/
void Game_quit_cmd()
{
    nusmv_assert(generic_commands_list != NODE_LIST(NULL));
    nusmv_assert(dependent_commands_list != NODE_LIST(NULL));
    nusmv_assert(specific_commands_list != NODE_LIST(NULL));

    NodeList_destroy(generic_commands_list);
    generic_commands_list = NODE_LIST(NULL);
    NodeList_destroy(dependent_commands_list);
    dependent_commands_list = NODE_LIST(NULL);
    NodeList_destroy(specific_commands_list);
    specific_commands_list = NODE_LIST(NULL);
}

/**Function********************************************************************

  Synopsis    [ Returns the list of generic commands. ]

  Description [ Returned list must not be modified. ]

  SideEffects [ ]

  SeeAlso     [ Game_cmd_get_dependent_commands,
                Game_cmd_get_specific_commands ]

******************************************************************************/
NodeList_ptr Game_cmd_get_generic_commands()
{
    nusmv_assert(generic_commands_list != NODE_LIST(NULL));
    return generic_commands_list;
}

/**Function********************************************************************

  Synopsis    [ Returns the list of dependent commands. ]

  Description [ Returned list must not be modified. ]

  SideEffects [ ]

  SeeAlso     [ Game_cmd_get_generic_commands,
                Game_cmd_get_specific_commands ]

******************************************************************************/
NodeList_ptr Game_cmd_get_dependent_commands()
{
    nusmv_assert(dependent_commands_list != NODE_LIST(NULL));
    return dependent_commands_list;
}

/**Function********************************************************************

  Synopsis    [ Returns the list of specific commands. ]

  Description [ Returned list must not be modified. ]

  SideEffects [ ]

  SeeAlso     [ Game_cmd_get_generic_commands,
                Game_cmd_get_dependent_commands ]

******************************************************************************/
NodeList_ptr Game_cmd_get_specific_commands()
{
    nusmv_assert(specific_commands_list != NODE_LIST(NULL));
    return specific_commands_list;
}

/*---------------------------------------------------------------------------*/
/* Definition of static functions                                            */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis           [ Read an XML file generated by the RATSY tool. ]

  CommandName        [ read_rat_file ]

  CommandSynopsis    [ Read an XML file generated by the RATSY tool. ]

  CommandArguments   [ \[-h\] \[-i file\] ]

  CommandDescription [ Reads an XML file generated by the RATSY
                       (formerly RAT) tool. If the <tt>-i</tt> option
                       is not specified, it reads from the file
                       specified in the environment variable
                       <tt>input_file</tt>.<p>

  Command options:<p>
  <dl>
    <dt> <tt>-h</tt>
       <dd> Prints the command usage.
    <dt> <tt>-i file</tt>
       <dd> Sets the environment variable <tt>input_file</tt> to
          <tt>file</tt>, and reads the model from the specified
          file.
  </dl> ]

  SideEffects        [ ]

  SeeAlso            [ CommandReadModel ]

******************************************************************************/
static int CommandReadRatFile(NuSMVEnv_ptr env,int argc, char** argv)
{
#if ! HAVE_LIBEXPAT
    fprintf(stderr,
            "The Expat XML library seems not to be avialable.\n"
                    "NuGaT cannot parse XML files without Expat.\n");
    return 1;
#else
    int c;
  char* input_file_name = (char*) NULL;
  const ErrorMgr_ptr errmgr =
                    ERROR_MGR(NuSMVEnv_get_value(env, ENV_ERROR_MANAGER));

  util_getopt_reset();
  while((c = util_getopt(argc, argv, "hi:")) != EOF) {
    switch(c) {
    case 'i':
      {
        input_file_name = ALLOC(char, strlen(util_optarg) + 1);
        strcpy(input_file_name, util_optarg);
        break;
      }
    case 'h': /* fall through */
    default:
      goto CommandReadRatFile_return_usage;
    }
  }
  if (argc != util_optind) goto CommandReadRatFile_return_usage;

  if (cmp_struct_get_read_model(cmps)) {
    fprintf(stderr,
            "A model appears to be already read from file: %s.\n",
            get_input_file(OptsHandler_create()));
    goto CommandReadRatFile_return_1;
  }

  if (input_file_name != (char*) NULL) {
    set_input_file(OptsHandler_create(), input_file_name);
  }

  if (get_input_file(OptsHandler_create()) == (char*) NULL) {
    fprintf(stderr,
            "Input file is (null). You must set the input file before.\n");
    goto CommandReadRatFile_return_1;
  }

  /* Parse the input file. */

  if (opt_verbose_level_gt(OptsHandler_create(), 0)) {
    fprintf(stderr,
            "Parsing RAT file \"%s\" ..... ",
            get_input_file(OptsHandler_create()));
    fflush(stderr);
  }

  if (Game_RatFileToGame(env,get_input_file(OptsHandler_create()))) {
    goto CommandReadRatFile_exit_1;
  }

  if (opt_verbose_level_gt(OptsHandler_create(), 0)) {
    fprintf(stderr, "done.\n");
    fflush(stderr);
  }

  cmp_struct_set_read_model(cmps);

  /* Clean up and exit. */

  /* Normal return. */
  if (input_file_name != (char*) NULL) FREE(input_file_name);
  return 0;

 CommandReadRatFile_exit_1:
  if (input_file_name != (char*) NULL) FREE(input_file_name);
  exit(1);

 CommandReadRatFile_return_1:
  if (input_file_name != (char*) NULL) FREE(input_file_name);
  return 1;

 CommandReadRatFile_return_usage:
  if (input_file_name != (char*) NULL) FREE(input_file_name);
  return UsageReadRatFile();
#endif /* !HAVE_LIBEXPAT  */
}

static int UsageReadRatFile()
{
    fprintf(stderr, "usage: read_rat_file [-h] [-i <file>]\n");
    fprintf(stderr, "   -h \t\tPrints the command usage.\n");
    fprintf(stderr, "   -i <file> \tReads the model from the specified "
            "RATSY project file.\n");
    return(1);
}

/**Function********************************************************************

  Synopsis           [ Flattens the hierarchy of modules. ]

  CommandName        [ flatten_hierarchy ]

  CommandSynopsis    [ Flattens the hierarchy of modules. ]

  CommandArguments   [ \[-h\] ]

  CommandDescription [ This command is responsible of the
                       instantiation of modules. The instantiation is
                       performed by substituting the actual parameters
                       for the formal parameters, and then by
                       prefixing the result via the instance name.

  Command options:<p>
  <dl>
    <dt> <tt>-h</tt>
       <dd> Prints the command usage.
  </dl><p> ]

  SideEffects        [ ]

  SeeAlso            [ CommandFlattenHierarchy ]

******************************************************************************/
static int CommandGameFlattenHierarchy(NuSMVEnv_ptr env,int argc, char** argv)
{
    int c;

    nusmv_assert(opt_game_game(OptsHandler_create()));

    util_getopt_reset();
    while ((c = util_getopt(argc, argv, "h")) != EOF) {
        switch (c) {
            case 'h': return UsageGameFlattenHierarchy();

            default:  return UsageGameFlattenHierarchy();
        }
    }

    if (argc != util_optind) return UsageGameFlattenHierarchy();

    if (cmp_struct_get_read_model(cmps) == 0) {
        fprintf(stderr,
                "A model must be read before. Use the \"read_model\" command.\n");
        return 1;
    }

    if (cmp_struct_get_flatten_hrc(cmps)) {
        fprintf(stderr, "The hierarchy has already been flattened.\n");
        return 1;
    }

    return Game_CommandFlattenHierarchy(env); /* does the work */
}

static int UsageGameFlattenHierarchy()
{
    fprintf(stderr, "usage: flatten_hierarchy [-h]\n");
    fprintf(stderr, "   -h \t\tPrints the command usage\n");
    return 1;
}

/**Function********************************************************************

  Synopsis           [ Builds the BDD variables necessary to compile the
                       model into BDD. ]

  CommandName        [ encode_variables ]

  CommandSynopsis    [ Builds the BDD variables necessary to compile the
                       model into BDD.]

  CommandArguments   [ \[-h\] \[-i order-file\] ]

  CommandDescription [ Generates the boolean BDD variables and the ADD
                       needed to encode propositionally the (symbolic)
                       variables declared in the model.<br>

                       The variables are created as default in the
                       order in which they appear in a depth first
                       traversal of the hierarchy.<p>

                       The input order file can be partial and can
                       contain variables not declared in the
                       model. Variables not declared in the model are
                       simply discarded. Variables declared in the
                       model which are not listed in the ordering
                       input file will be created and appended at the
                       end of the given ordering list, according to
                       the default ordering.<p>

  Command options:<p>
  <dl>
    <dt> <tt>-h</tt>
       <dd> Prints the command usage.
    <dt> <tt>-i order-file</tt>
       <dd> Sets the environment variable <tt>input_order_file</tt> to
       <tt>order-file</tt>, and reads the variable ordering to be used from
       file <tt>order-file</tt>. This can be combined with the
       <tt>write_order</tt> command. The variable ordering is written to a
       file, which can be inspected and reordered by the user, and then
       read back in.
  </dl> ]

  SideEffects        [ ]

  SeeAlso            [ CommandEncodeVariables, compile_encode_variables ]

******************************************************************************/
static int CommandGameEncodeVariables(NuSMVEnv_ptr env,int argc, char** argv)
{
    int c;
    char* input_order_file_name = NIL(char);

    nusmv_assert(opt_game_game(OptsHandler_create()));

    util_getopt_reset();
    while ((c = util_getopt(argc,argv,"i:h")) != EOF) {
        switch (c) {
            case 'i':
                input_order_file_name = ALLOC(char, strlen(util_optarg)+1);
                strcpy(input_order_file_name, util_optarg);
                break;

            case 'h':
                goto command_game_encode_variables_return_usage;

            default:
                goto command_game_encode_variables_return_usage;
        }
    }

    if (argc != util_optind) {
        goto command_game_encode_variables_return_usage;
    }

    /* pre-conditions: */
    if (Compile_check_if_flattening_was_built(env,stderr)) {
        goto command_game_encode_variables_return_1;
    }

    if (cmp_struct_get_encode_variables(cmps)) {
        fprintf(stderr, "The variables appear to be already built.\n");
        goto command_game_encode_variables_return_1;
    }

    Game_CommandEncodeVariables(env,input_order_file_name);

    if (input_order_file_name != NIL(char)) FREE(input_order_file_name);
    return 0;

    command_game_encode_variables_return_1:
    if (input_order_file_name != NIL(char)) FREE(input_order_file_name);
    return 1;

    command_game_encode_variables_return_usage:
    if (input_order_file_name != NIL(char)) FREE(input_order_file_name);
    return UsageGameEncodeVariables();
}

static int UsageGameEncodeVariables()
{
    fprintf(stderr, "usage: encode_variables [-h] [-i <file>]\n");
    fprintf(stderr, "   -h \t\tPrints the command usage.\n");
    fprintf(stderr, "   -i <file> \tReads variable ordering from file "
            "<file>.\n");
    return 1;
}

/**Function********************************************************************

  Synopsis           [ Compiles the flattened hierarchy into BDD. ]

  CommandName        [ build_model ]

  CommandSynopsis    [ Compiles the flattened hierarchy into BDD. ]

  CommandArguments   [ \[-h\] \[-f\] \[-m Method\] ]

  CommandDescription [ Compiles the flattened hierarchy into BDD
                       (initial states, invariants, and transition
                       relation) using the method specified in the
                       environment variable <tt>partition_method</tt>
                       for building the transition relation.<p>

  Command options:<p>
  <dl>
    <dt> <tt>-h</tt>
       <dd> Prints the command usage.
    <dt> <tt>-m Method</tt>
       <dd> Sets the environment variable <tt>partition_method</tt> to
           the value <tt>Method</tt>, and then builds the transition
           relation. Available methods are <code>Monolithic</code>,
           <code>Threshold</code> and <code>Iwls95CP</code>.
    <dt> <tt>-f</tt>
       <dd> Forces model construction. By default, only one partition
            method is allowed. This option allows to overcome this
            default, and to build the transition relation with different
            partitioning methods.
  </dl> ]

  SideEffects        [ ]

  SeeAlso            [ CommandBuildModel, compile_build_model,
                       compile_create_flat_model ]

******************************************************************************/
static int CommandGameBuildModel(NuSMVEnv_ptr env,int argc, char** argv)
{
    int c;
    boolean force_build = false;
    char* partition_method = NIL(char);

    nusmv_assert(opt_game_game(OptsHandler_create()));

    util_getopt_reset();
    while((c = util_getopt(argc,argv,"m:fh")) != EOF){
        switch(c){
            case 'm': {
                partition_method = ALLOC(char, strlen(util_optarg)+1);
                strcpy(partition_method, util_optarg);
                break;
            }

            case 'f': {
                force_build = true;
                break;
            }

            case 'h':
                goto command_game_build_model_return_usage;

            default:
                goto command_game_build_model_return_usage;
        }
    }
    if (argc != util_optind) {
        goto command_game_build_model_return_usage;
    }

    /* pre-conditions: */
    if (Compile_check_if_encoding_was_built(env,stderr)) {
        goto command_game_build_model_return_1;
    }

    if (!force_build && cmp_struct_get_build_model(cmps)) {
        fprintf(stderr,
                "A model appears to be already built from file: %s.\n",
                get_input_file(OptsHandler_create()));
        goto command_game_build_model_return_1;
    }

    if (partition_method != NIL(char)) {
        if (TransType_from_string(partition_method) != TRANS_TYPE_INVALID) {
            if ((force_build) &&
                (TransType_from_string(partition_method) ==
                 get_partition_method(OptsHandler_create()))) {
                if (cmp_struct_get_build_model(cmps)) {
                    fprintf(stderr,
                            "A model for the chosen method has already been "
                                    "constructed.\n");
                    goto command_game_build_model_return_1;
                }
            }
            set_partition_method(OptsHandler_create(),
                                 TransType_from_string(partition_method));
        } else {
            fprintf(stderr,
                    "The only possible values for \"-m\" option are:\n\t");
            print_partition_method(stderr);
            fprintf(stderr, "\n");
            goto command_game_build_model_return_1;
        }
    }

    Game_CommandBuildFlatModel(env);
    cmp_struct_set_build_flat_model(cmps);

    Game_CommandBuildBddModel(env);
    cmp_struct_set_build_model(cmps);

    if (opt_verbose_level_gt(OptsHandler_create(), 0)) {
        fprintf(stderr,
                "\nThe model has been built from file %s.\n",
                get_input_file(OptsHandler_create()));
    }

    if (partition_method != NIL(char)) FREE(partition_method);
    return 0;

    command_game_build_model_return_1:
    if (partition_method != NIL(char)) FREE(partition_method);
    return 1;

    command_game_build_model_return_usage:
    if (partition_method != NIL(char)) FREE(partition_method);
    return UsageGameBuildModel();
}

static int UsageGameBuildModel()
{
    fprintf(stderr, "usage: build_model [-h] [-f] [-m Method]\n");
    fprintf(stderr, "   -h \t\tPrints the command usage\n");
    fprintf(stderr, "   -m Method \tUses \"Method\" as partitioning method, "
            "and set it as default method\n");
    fprintf(stderr, "\t\tto be used in the following image computations.\n");
    fprintf(stderr, "\t\tThe currently available methods are:\n\t\t");
    print_partition_method(stderr);
    fprintf(stderr, "\n   -f \t\tForces the model re-construction, even if "
            "a model has already been built\n");
    return 1;
}

/**Function********************************************************************

  Synopsis           [ Compiles the flattened hierarchy into SEXP. ]

  CommandName        [ build_flat_model ]

  CommandSynopsis    [ Compiles the flattened hierarchy into SEXP. ]

  CommandArguments   [ \[-h\] ]

  CommandDescription [ Compiles the flattened hierarchy into SEXP
                       (initial states, invariants, and transition
                       relation).<p>

  Command options:<p>
  <dl>
    <dt> <tt>-h</tt>
       <dd> Prints the command usage.
  </dl> ]

  SideEffects        [ ]

  SeeAlso            [ CommandBuildFlatModel, compile_create_flat_model ]

******************************************************************************/
static int CommandGameBuildFlatModel(NuSMVEnv_ptr env,int argc, char** argv)
{
    int c;

    nusmv_assert(opt_game_game(OptsHandler_create()));

    util_getopt_reset();
    while((c = util_getopt(argc,argv,"h")) != EOF){
        switch(c){
            case 'h': return(UsageGameBuildFlatModel());

            default:  return(UsageGameBuildFlatModel());
        }
    }
    if (argc != util_optind) return(UsageGameBuildFlatModel());

    /* pre-conditions: */
    if (Compile_check_if_flattening_was_built(env,stderr)) return 1;

    if (cmp_struct_get_build_flat_model(cmps)) {
        fprintf(stderr,
                "A model appears to be already built from file: %s.\n",
                get_input_file(OptsHandler_create()));
        return 1;
    }

    Game_CommandBuildFlatModel(env);
    cmp_struct_set_build_flat_model(cmps);

    if (opt_verbose_level_gt(OptsHandler_create(), 0)) {
        fprintf(stderr,
                "\nThe sexp model has been built from file %s.\n",
                get_input_file(OptsHandler_create()));
    }

    return 0;
}

static int UsageGameBuildFlatModel()
{
    fprintf(stderr, "usage: build_flat_model [-h]\n");
    fprintf(stderr, "   -h \t\tPrints the command usage.\n");
    return 1;
}

/**Function********************************************************************

  Synopsis           [ Compiles the flattened hierarchy into boolean SEXP. ]

  CommandName        [ build_boolean_model ]

  CommandSynopsis    [ Compiles the flattened hierarchy into boolean SEXP. ]

  CommandArguments   [ \[-h\] \[-f\] ]

  CommandDescription [ Compiles the flattened hierarchy into boolean
                       SEXP (initial states, invariants, and
                       transition relation).<p>

  Command options:<p>
  <dl>
    <dt> <tt>-h</tt>
       <dd> Prints the command usage.
    <dt> <tt>-f</tt>
       <dd> Forces the boolean model construction.
  </dl> ]

  SideEffects        [ ]

  SeeAlso            [ CommandBuildBooleanModel, compile_create_flat_model,
                       compile_create_boolean_model ]

******************************************************************************/
static int CommandGameBuildBooleanModel(NuSMVEnv_ptr env,int argc, char ** argv)
{
    int c;
    boolean forced = false;

    nusmv_assert(opt_game_game(OptsHandler_create()));

    util_getopt_reset();
    while((c = util_getopt(argc,argv,"hf")) != EOF){
        switch(c){
            case 'h': return(UsageGameBuildBooleanModel());

            case 'f': forced = true; break;

            default:  return(UsageGameBuildBooleanModel());
        }
    }
    if (argc != util_optind) return(UsageGameBuildBooleanModel());

    /* pre-conditions: */
    if (Compile_check_if_encoding_was_built(env,stderr)) return 1;

    if (cmp_struct_get_build_bool_model(cmps) && !forced) {
        fprintf(stderr,
                "A model appears to be already built from file: %s.\n",
                get_input_file(OptsHandler_create()));
        return 1;
    }

    Game_CommandBuildFlatModel(env);
    cmp_struct_set_build_flat_model(cmps);

    Game_CommandBuildBooleanModel(env);
    cmp_struct_set_build_bool_model(cmps);

    if (opt_verbose_level_gt(OptsHandler_create(), 0)) {
        fprintf(stderr,
                "\nThe boolean sexp model has been built from file %s.\n",
                get_input_file(OptsHandler_create()));
    }

    return 0;
}

static int UsageGameBuildBooleanModel()
{
    fprintf(stderr, "usage: build_boolean_model [-h][-f]\n");
    fprintf(stderr, "   -h \t\tPrints the command usage.\n");
    fprintf(stderr, "   -f \t\tForces the boolean model construction.\n");
    return 1;
}

/**Function********************************************************************

  Synopsis           [ Writes the currently loaded SMV model in the specified
                       file, after having flattened it. ]

  CommandName        [ write_flat_model ]

  CommandSynopsis    [ Writes a flat model of a given SMV file. ]

  CommandArguments   [ \[-h\] \[-o filename\] ]

  CommandDescription [ A corresponding equivalent model is printed
                       out.  If no file is specified, the file
                       specified with the environment variable
                       <tt>output_flatten_model_file</tt> is used if
                       any, otherwise standard output is used as
                       output. <p>

  Command options:<p>
  <dl>
    <dt> <tt>-h</tt>
       <dd> Prints the command usage.
    <dt><tt>-o filename</tt>
       <dd> Attempts to write the flat SMV model in <tt>filename</tt>.
  </dl> ]

  SideEffects        [ ]

  SeeAlso            [ CommandWriteModelFlat ]

******************************************************************************/
static int CommandGameWriteModelFlat(NuSMVEnv_ptr env,int argc, char **argv)
{
    int c = 0;
    int rv = 0;
    char* output_file = NIL(char);
    FILE* ofileid = NIL(FILE);
    int bSpecifiedFilename = FALSE;
    ErrorMgr_ptr const errmgr =
            ERROR_MGR(NuSMVEnv_get_value(env, ENV_ERROR_MANAGER));

    nusmv_assert(opt_game_game(OptsHandler_create()));

    util_getopt_reset();
    while ((c = util_getopt(argc, argv, "ho:")) != EOF) {
        switch (c) {
            case 'h':
                goto command_game_write_model_flat_return_usage;

            case 'o':
                if (bSpecifiedFilename == TRUE) {
                    goto command_game_write_model_flat_return_usage;
                }
                output_file = ALLOC(char, strlen(util_optarg)+1);
                nusmv_assert(output_file);
                strcpy(output_file, util_optarg);
                bSpecifiedFilename = TRUE;
                break;

            default:
                break;
        }
    }

    if (argc != util_optind) {
        goto command_game_write_model_flat_return_usage;
    }

    if (output_file == NIL(char)) {
        output_file = get_output_flatten_model_file(OptsHandler_create());
    }
    if (output_file == NIL(char)) {
        ofileid = stdout;
    } else {
        ofileid = fopen(output_file, "w");
        if (ofileid == NULL) {
            fprintf(stderr, "Unable to open file \"%s\".\n", output_file);
            goto command_game_write_model_flat_return_1;
        }
    }

    /* pre-conditions: */
    if (Compile_check_if_flattening_was_built(env,stderr)) {
        goto command_game_write_model_flat_return_1;
    }

    if (opt_verbose_level_gt(OptsHandler_create(), 0)) {
        fprintf(stderr, "Writing flat model into file \"%s\"..",
                output_file == (char *)NULL ? "stdout" : output_file);
    }

    CATCH(errmgr) {
            Game_CommandWriteFlatModel(env,ofileid);

            if (opt_verbose_level_gt(OptsHandler_create(), 0)) {
                fprintf(stderr, ".. done.\n");
            }
        }
    FAIL(errmgr) {
        rv = 1;
    }
    fflush(ofileid);

    if (ofileid != stdout) {
        fclose(ofileid);
        if (bSpecifiedFilename) FREE(output_file);
    }
    return rv;

    command_game_write_model_flat_return_1:
    if (ofileid != stdout) {
        fclose(ofileid);
        if (bSpecifiedFilename == TRUE) FREE(output_file);
    }
    return 1;

    command_game_write_model_flat_return_usage:
    if (ofileid != stdout) {
        fclose(ofileid);
        if (bSpecifiedFilename == TRUE) FREE(output_file);
    }
    return UsageGameWriteModelFlat();
}

static int UsageGameWriteModelFlat(void)
{
    fprintf(stderr, "usage: write_flat_model [-h] [-o filename]\n");
    fprintf(stderr, "  -h \t\tPrints the command usage.\n");
    fprintf(stderr, "  -o filename\tWrites output to \"filename\"\n");
    return 1;
}

/**Function********************************************************************

  Synopsis           [ Writes a flat and boolean model of a given SMV file. ]

  CommandName        [ write_boolean_model ]

  CommandSynopsis    [ Writes a flattened and booleanized model of a
                       given SMV file. ]

  CommandArguments   [ \[-h\] \[-o filename\] ]

  CommandDescription [ Writes the currently loaded SMV model in the
                       specified file, after having flattened and
                       booleanized it.

                       If no file is specified, the file specified via
                       the environment variable
                       <tt>output_boolean_model_file</tt> is used if
                       any, otherwise standard output is used. <p>

                       ** New in 2.4.0 and later **
                       Scalar variables are dumped as DEFINEs whose
                       body is their boolean encoding.

                       This allows the user to still express and see
                       parts of the generated boolean model in terms
                       of the original model's scalar variables names
                       and values, and still keeping the generated
                       model purely boolean.

                       Also, symbolic constants are dumped within a
                       CONSTANTS statement to declare the values of
                       the original scalar variables' for future
                       reading of the generated file.]

  Command options:<p>
  <dl>
    <dt> <tt>-h</tt>
       <dd> Prints the command usage.
    <dt><tt>-o filename</tt>
       <dd> Attempts to write the flat and boolean SMV model in
       <tt>filename</tt>.
  </dl>

  SideEffects        [ ]

  SeeAlso            [ CommandWriteModelFlatBool ]

******************************************************************************/
static int CommandGameWriteModelFlatBool(NuSMVEnv_ptr env,int argc, char** argv)
{
    int c = 0;
    int rv = 0;
    char* output_file = NIL(char);
    FILE* ofileid = NIL(FILE);
    int bSpecifiedFilename = FALSE;
    ErrorMgr_ptr const errmgr =
            ERROR_MGR(NuSMVEnv_get_value(env, ENV_ERROR_MANAGER));

    nusmv_assert(opt_game_game(OptsHandler_create()));

    util_getopt_reset();
    while ((c = util_getopt(argc, argv, "ho:")) != EOF) {
        switch (c) {
            case 'h':
                if (bSpecifiedFilename == TRUE) FREE(output_file);
                return UsageGameWriteModelFlatBool();

            case 'o':
                output_file = ALLOC(char, strlen(util_optarg)+1);
                nusmv_assert(output_file);
                strcpy(output_file, util_optarg);
                bSpecifiedFilename = TRUE;
                break;

            default:
                break;
        }
    }

    if (argc != util_optind) {
        if (bSpecifiedFilename == TRUE) FREE(output_file);
        return UsageGameWriteModelFlatBool();
    }

    if (output_file == NIL(char)) {
        output_file = get_output_boolean_model_file(OptsHandler_create());
    }

    if (output_file == NIL(char)) {
        ofileid = stdout;
    } else {
        ofileid = fopen(output_file, "w");
        if (ofileid == NULL) {
            fprintf(stderr, "Unable to open file \"%s\".\n", output_file);
            if (bSpecifiedFilename == TRUE)  FREE(output_file);
            return 1;
        }
    }

    if (Compile_check_if_bool_model_was_built(env,stderr, true)) {
        if (ofileid != stdout) {
            fclose(ofileid);
            if (bSpecifiedFilename == TRUE) FREE(output_file);
        }
        return 1;
    }

    if (opt_verbose_level_gt(OptsHandler_create(), 0)) {
        fprintf(stderr,
                "Writing boolean model into file \"%s\"..",
                output_file == (char *)NULL ? "stdout" : output_file);
    }

    CATCH(errmgr) {
            Game_CommandWriteBooleanModel(env,ofileid);

            if (opt_verbose_level_gt(OptsHandler_create(), 0)) {
                fprintf(stderr, ".. done.\n");
            }
        } FAIL(errmgr) {
        rv = 1;
    }
    fflush(ofileid);

    if (ofileid != stdout) {
        fclose(ofileid);
        if (bSpecifiedFilename == TRUE)  FREE(output_file);
    }
    return rv;
}

static int UsageGameWriteModelFlatBool(void)
{
    fprintf(stderr, "usage: write_boolean_model [-h] [-o filename]\n");
    fprintf(stderr, "  -h \t\tPrints the command usage.\n");
    fprintf(stderr, "  -o filename\tWrites output to \"filename\".\n");
    return 1;
}

/**Function********************************************************************

  Synopsis           [ Checks properties. ]

  CommandName        [ check_property ]

  CommandSynopsis    [ Checks one or more properties in the current list
                       of properties. ]

  CommandArguments   [ \[-h\] \[\[-n number\] | \[\[-r (1|2)\]
                       \[(-a | -A | -d | -D | -b | -l | -g)\]\]\] ]

  CommandDescription [ Checks the specified properties taken from the
                       property list. Either a number or a
                       (combination of) player and property type can
                       be given.

  <p>
  Command options:<p>
  <dl>
    <dt> <tt>-h</tt>
       <dd> Prints the command usage.
    <dt> <tt>-n number</tt>
       <dd> Checks the property with id <tt>number</tt> in the
            property list if it exists.
    <dt> <tt>-r (1|2)</tt>
       <dd> Checks the properties of player 1|2 not already checked.
    <dt> <tt>-a/tt>
       <dd> Checks all the REACHTARGET properties not already checked.
    <dt> <tt>-A/tt>
       <dd> Checks all the AVOIDTARGET properties not already checked.
    <dt> <tt>-d/tt>
       <dd> Checks all the REACHDEADLOCK properties not already checked.
    <dt> <tt>-D/tt>
       <dd> Checks all the AVOIDDEADLOCK properties not already checked.
    <dt> <tt>-b/tt>
       <dd> Checks all the BUCHIGAME properties not already checked.
    <dt> <tt>-l/tt>
       <dd> Checks all the LTLGAME properties not already checked.
    <dt> <tt>-g/tt>
       <dd> Checks all the GENREACTIVITY properties not already checked.
  </dl> ]

  SideEffects        [ ]

  SeeAlso            [ CommandCheckProperty ]

******************************************************************************/
static int CommandGameCheckProperty(NuSMVEnv_ptr env,int argc, char** argv)
{
    int c = 0;
    int prop_no = -1;
    PropGame_Type pt = Prop_NoType;
    int player_no = 0; /* Valid values only 1 and 2. */
    ErrorMgr_ptr const errmgr =
            ERROR_MGR(NuSMVEnv_get_value(env, ENV_ERROR_MANAGER));
    PropDb_ptr prop_db  = PROP_DB(NuSMVEnv_get_value(env, ENV_PROP_DB));

    nusmv_assert(opt_game_game(OptsHandler_create()));

    util_getopt_reset();
    while((c = util_getopt(argc, argv, "hn:r:aAdDblg")) != EOF){
        switch(c){
            case 'h': return UsageGameCheckProperty();
            case 'n':
            {
                if (pt != Prop_NoType) return UsageGameCheckProperty();
                if (prop_no != -1) return UsageGameCheckProperty();
                if (player_no != 0) return UsageGameCheckProperty();

                prop_no = PropDb_get_prop_index_from_string(prop_db,
                                                            util_optarg);
                if (prop_no == -1) return 1;

                break;
            }
            case 'r':
            {
                char* strNumber;

                if (prop_no != -1) return UsageGameCheckProperty();
                if (player_no != 0) return UsageGameCheckProperty();

                strNumber = util_strsav(util_optarg);
                if (util_str2int(strNumber, &player_no) != 0) {
                    FREE(strNumber);
                    return UsageGameCheckProperty();
                }
                if (player_no != 1 && player_no != 2) {
                    FREE(strNumber);
                    return UsageGameCheckProperty();
                }

                FREE(strNumber);
                break;
            }
            case 'a':
            {
                if (pt != Prop_NoType) return UsageGameCheckProperty();
                if (prop_no != -1) return UsageGameCheckProperty();
                pt = PropGame_ReachTarget;
                break;
            }
            case 'A':
            {
                if (pt != Prop_NoType) return UsageGameCheckProperty();
                if (prop_no != -1) return UsageGameCheckProperty();
                pt = PropGame_AvoidTarget;
                break;
            }
            case 'd':
            {
                if (pt != Prop_NoType) return UsageGameCheckProperty();
                if (prop_no != -1) return UsageGameCheckProperty();
                pt = PropGame_ReachDeadlock;
                break;
            }
            case 'D':
            {
                if (pt != Prop_NoType) return UsageGameCheckProperty();
                if (prop_no != -1) return UsageGameCheckProperty();
                pt = PropGame_AvoidDeadlock;
                break;
            }
            case 'l':
            {
                if (pt != Prop_NoType) return UsageGameCheckProperty();
                if (prop_no != -1) return UsageGameCheckProperty();
                pt = PropGame_LtlGame;
                break;
            }
            case 'b':
            {
                if (pt != Prop_NoType) return UsageGameCheckProperty();
                if (prop_no != -1) return UsageGameCheckProperty();
                pt = PropGame_BuchiGame;
                break;
            }
            case 'g':
            {
                if (pt != Prop_NoType) return UsageGameCheckProperty();
                if (prop_no != -1) return UsageGameCheckProperty();
                pt = PropGame_GenReactivity;
                break;
            }
            default:
                return UsageGameCheckProperty();
        }
    }
    if (argc != util_optind) return UsageGameCheckProperty();

    /* command hierarchy control */
    if (Compile_check_if_model_was_built(env,stderr, false)) return 1;

    if (prop_no != -1) {
        CATCH(errmgr) {
                Prop_ptr prop;

                /* If this is PropGame_LtlGame, then check whether Boolean model
                   has been built. */
                prop = PropDb_get_prop_at_index(prop_db, prop_no);
                if ((prop != PROP(NULL)) && (Prop_get_type(prop) == PropGame_LtlGame)) {
                    if (Compile_check_if_bool_model_was_built(env,stderr, false)) {
                        return 1;
                    }
                }

                PropDb_verify_prop_at_index(prop_db, prop_no);
            }
        FAIL(errmgr) {
            return 1;
        }
    } else {
        PropDbGame_ptr pdb = PROP_DB_GAME(prop_db);
        string_ptr player_str = (string_ptr) NULL;

        if (player_no == 1) {
            player_str = UStringMgr_find_string(USTRING_MGR(NuSMVEnv_get_value(env, ENV_STRING_MGR)),PLAYER_NAME_1);
        } else if (player_no == 2) {
            player_str = UStringMgr_find_string(USTRING_MGR(NuSMVEnv_get_value(env, ENV_STRING_MGR)),PLAYER_NAME_2);
        } else {
            nusmv_assert(player_no == 0);
        }

        CATCH(errmgr) {
                int i;

                /* If there are PropGame_LtlGame, then check whether Boolean
                   model has been built. */
                for (i = 0; i < PropDb_get_size(PROP_DB(pdb)); ++i) {
                    PropGame_ptr p = PROP_GAME(PropDb_get_prop_at_index(PROP_DB(pdb), i));
                    if (((pt == Prop_NoType) ||
                         (Prop_get_type(PROP(p)) == pt)) &&
                        ((player_str == (string_ptr) NULL) ||
                         (PropGame_get_player(p) == player_str))) {
                        if ((Prop_get_type(PROP(p)) == PropGame_LtlGame) &&
                            Compile_check_if_bool_model_was_built(env,stderr, false)) {
                            return 1;
                        }
                    }
                }

                PropDbGame_verify_all_type_player(pdb, pt, player_str);
            }
        FAIL(errmgr) {
            return 1;
        }
    }

    return 0;
}

static int UsageGameCheckProperty()
{
    fprintf(stderr, "usage: check_property [-h]\n" \
      "       [[-n number] | [[-r 1|2] [-a | -A | -d | -D | -b | -l | -g]]]\n");
    fprintf(stderr, "  -h \t\t Prints the command usage.\n");
    fprintf(stderr, "  -n number \t Checks property number.\n");
    fprintf(stderr, "  -r 1|2 \t Checks properties of player 1|2.\n");
    fprintf(stderr, "  -a \t\t Checks REACHTARGET properties.\n");
    fprintf(stderr, "  -A \t\t Checks AVOIDTARGET properties.\n");
    fprintf(stderr, "  -d \t\t Checks REACHDEADLOCK properties.\n");
    fprintf(stderr, "  -D \t\t Checks AVOIDDEADLOCK properties.\n");
    fprintf(stderr, "  -b \t\t Checks BUCHIGAME properties.\n");
    fprintf(stderr, "  -l \t\t Checks LTLGAME properties.\n");
    fprintf(stderr, "  -g \t\t Checks GENREACTIVITY properties.\n");
    return 1;
}

/**Function********************************************************************

  Synopsis           [ Shows properties. ]

  CommandName        [ show_property ]

  CommandSynopsis    [ Shows one or more properties in the current list
                       of properties. ]

  CommandArguments   [ \[-h\] \[-s\] \[-m | -o output-file\]
                       \[\[-n number\] | \[\[-u | -t | -f\] \[-r (1|2)\]
                         \[(-a | -A | -d | -D | -b | -l | -g)\]\]\] ]

  CommandDescription [ Show the specified properties taken from the
                       property list. Either a number or a
                       (combination of) status and player and property
                       type can be given. <p>

                       For every property, the following informations
                       are displayed:
                       <ul>
                       <li>the identifier of the property (a
                           progressive number);
                       <li>the property formula;
                       <li>the type (ReachTarget, AvoidTarget, etc.);
                       <il>the status of the formula (Unchecked, True,
                           False);
                       <li>if the formula has been found to be false,
                           the number of the corresponding
                           counterexample trace.
                       </ul>
                       <p>

                       By default, all the properties currently stored
                       in the list of properties are shown. Specifying
                       the suitable options, it is possible to let the
                       system show a restricted set of properties. It
                       is allowed to insert only one option per status
                       and one option per type. <p>

  Command options:<p>
  <dl>
    <dt> <tt>-h</tt>
       <dd> Prints the command usage.
    <dt> <tt>-m</tt>
       <dd> Pipes the output through the program specified by the
       <tt>PAGER</tt> shell variable if defined, else through the
       <tt>UNIX</tt> "more" command.
    <dt> <tt>-o output-file</tt>
       <dd> Writes the output generated by the command to
       <tt>output-file<\tt>.
    <dt> <tt>-s Prints the number of stored properties. </tt>
       <dd> <\tt>.
    <dt> <tt>-u</tt>
       <dd> Prints only unchecked properties.
    <dt> <tt>-t</tt>
       <dd> Prints only those properties found to be true.
    <dt> <tt>-f</tt>
       <dd> Prints only those properties found to be false.
    <dt> <tt>-n number</tt>
       <dd> Prints the property with number <tt>number</tt>.
    <dt> <tt>-r (1|2)</tt>
       <dd> Prints only the properties of player 1|2.
    <dt> <tt>-t/tt>
       <dd> Prints only the REACHTARGET properties.
    <dt> <tt>-T/tt>
       <dd> Prints only the AVOIDTARGET properties.
    <dt> <tt>-d/tt>
       <dd> Prints only the REACHDEADLOCK properties.
    <dt> <tt>-D/tt>
       <dd> Prints only the AVOIDDEADLOCK properties.
    <dt> <tt>-b/tt>
       <dd> Prints only the BUCHIGAME properties.
    <dt> <tt>-l/tt>
       <dd> Prints only the LTLGAME properties.
    <dt> <tt>-g/tt>
       <dd> Prints only the GENREACTIVITY properties.
  </dl> ]

  SideEffects        [ ]

  SeeAlso            [ CommandShowProperty ]

******************************************************************************/
static int CommandGameShowProperty(NuSMVEnv_ptr env,int argc, char** argv)
{
    int c;
    int retval = 0;
    boolean print_props_num = false;
    char* outFileName = NIL(char);
    FILE* old_stdout = NULL;
    int useMore = 0;
    Prop_Status status = Prop_NoStatus;
    int prop_no = -1;
    int player_no = 0; /* Valid values only 1 and 2. */
    Prop_Type type = Prop_NoType;
    ErrorMgr_ptr const errmgr =
            ERROR_MGR(NuSMVEnv_get_value(env, ENV_ERROR_MANAGER));
    PropDb_ptr prop_db  = PROP_DB(NuSMVEnv_get_value(env, ENV_PROP_DB));

    nusmv_assert(opt_game_game(OptsHandler_create()));

    util_getopt_reset();
    while((c = util_getopt(argc, argv, "hsmo:utfn:r:aAdDblg")) != EOF) {
        switch(c){
            case 'h':
            {
                if (outFileName != NIL(char)) FREE(outFileName);
                return UsageGameShowProperty();
            }
            case 's':
            {
                print_props_num = true;
                break;
            }
            case 'm':
            {
                if (outFileName != NIL(char)) {
                    FREE(outFileName);
                    return UsageGameShowProperty();
                }
                useMore = 1;
                break;
            }
            case 'o':
            {
                if (useMore == 1 || outFileName != NIL(char)) {
                    if (outFileName != NIL(char)) FREE(outFileName);
                    return UsageGameShowProperty();
                }
                outFileName = util_strsav(util_optarg);
                break;
            }
            case 'n':
            {
                if ((status != Prop_NoStatus) ||
                    (type != Prop_NoType)     ||
                    (player_no != 0)          ||
                    (prop_no != -1)) {
                    if (outFileName != NIL(char)) FREE(outFileName);
                    return UsageGameShowProperty();
                }

                prop_no = PropDb_get_prop_index_from_string(prop_db,
                                                            util_optarg);
                if (prop_no == -1) {
                    if (outFileName != NIL(char)) FREE(outFileName);
                    return(1);
                }

                break;
            }
            case 'u':
            {
                if ((status != Prop_NoStatus) || (prop_no != -1)) {
                    if (outFileName != NIL(char)) FREE(outFileName);
                    return UsageGameShowProperty();
                }
                status = Prop_Unchecked;
                break;
            }
            case 't':
            {
                if ((status != Prop_NoStatus) || (prop_no != -1)) {
                    if (outFileName != NIL(char)) FREE(outFileName);
                    return UsageGameShowProperty();
                }
                status = Prop_True;
                break;
            }
            case 'f':
            {
                if ((status != Prop_NoStatus) || (prop_no != -1)) {
                    if (outFileName != NIL(char)) FREE(outFileName);
                    return UsageGameShowProperty();
                }
                status = Prop_False;
                break;
            }
            case 'r':
            {
                char* strNumber;

                if ((player_no != 0) || (prop_no != -1)) {
                    if (outFileName != NIL(char)) FREE(outFileName);
                    return UsageGameShowProperty();
                }

                strNumber = util_strsav(util_optarg);
                if (util_str2int(strNumber, &player_no) != 0) {
                    FREE(strNumber);
                    if (outFileName != NIL(char)) FREE(outFileName);
                    return UsageGameCheckProperty();
                }
                if (player_no != 1 && player_no != 2) {
                    FREE(strNumber);
                    if (outFileName != NIL(char)) FREE(outFileName);
                    return UsageGameCheckProperty();
                }

                FREE(strNumber);
                break;
            }
            case 'a':
            {
                if ((type != Prop_NoType) || (prop_no != -1)) {
                    if (outFileName != NIL(char)) FREE(outFileName);
                    return UsageGameShowProperty();
                }
                type = PropGame_ReachTarget;
                break;
            }
            case 'A':
            {
                if ((type != Prop_NoType) || (prop_no != -1)) {
                    if (outFileName != NIL(char)) FREE(outFileName);
                    return UsageGameShowProperty();
                }
                type = PropGame_AvoidTarget;
                break;
            }
            case 'd':
            {
                if ((type != Prop_NoType) || (prop_no != -1)) {
                    if (outFileName != NIL(char)) FREE(outFileName);
                    return UsageGameShowProperty();
                }
                type = PropGame_ReachDeadlock;
                break;
            }
            case 'D':
            {
                if ((type != Prop_NoType) || (prop_no != -1)) {
                    if (outFileName != NIL(char)) FREE(outFileName);
                    return UsageGameShowProperty();
                }
                type = PropGame_AvoidDeadlock;
                break;
            }
            case 'b':
            {
                if ((type != Prop_NoType) || (prop_no != -1)) {
                    if (outFileName != NIL(char)) FREE(outFileName);
                    return UsageGameShowProperty();
                }
                type = PropGame_BuchiGame;
                break;
            }
            case 'l':
            {
                if ((type != Prop_NoType) || (prop_no != -1)) {
                    if (outFileName != NIL(char)) FREE(outFileName);
                    return UsageGameShowProperty();
                }
                type = PropGame_LtlGame;
                break;
            }
            case 'g':
            {
                if ((type != Prop_NoType) || (prop_no != -1)) {
                    if (outFileName != NIL(char)) FREE(outFileName);
                    return UsageGameShowProperty();
                }
                type = PropGame_GenReactivity;
                break;
            }
            default:
            {
                if (outFileName != NIL(char)) FREE(outFileName);
                return UsageGameShowProperty();
            }
        }
    }

    if (argc != util_optind) {
        if (outFileName != NIL(char)) FREE(outFileName);
        return UsageGameShowProperty();
    }

    /* command hierarchy control */
    if (Compile_check_if_flattening_was_built(env,stderr)) {
        if (outFileName != NIL(char)) FREE(outFileName);
        return 1;
    }

    if (useMore == 1) {
        nusmv_assert(outFileName == NIL(char));
        old_stdout = stdout;
        stdout = CmdOpenPipe(env,useMore);
        if (stdout == NIL(FILE)) {
            stdout = old_stdout;
            return(1);
        }
    }
    if (outFileName != NIL(char)) {
        old_stdout = stdout;
        stdout = CmdOpenFile(env,outFileName);
        if (stdout == NIL(FILE)) {
            stdout = old_stdout;
            FREE(outFileName);
            return(1);
        }
    }

    if (print_props_num) {
        fprintf(stdout, "Current number of stored properties: %d\n",
                PropDb_get_size(prop_db));
        if (useMore) {
            CmdClosePipe(stdout);
            stdout = old_stdout;
        }
        if (outFileName != NIL(char)) {
            CmdCloseFile(stdout);
            stdout = old_stdout;
            FREE(outFileName);
        }
        return 0;
    }
    OStream_ptr ostream_ptr_nusmv_output = OStream_create(stdout);
    PropDb_print_list_header(prop_db, ostream_ptr_nusmv_output);
    if (prop_no != -1) {
        retval = PropDb_print_prop_at_index(prop_db,
                                            ostream_ptr_nusmv_output,
                                            prop_no);
    } else {
        PropDbGame_ptr pdb = PROP_DB_GAME(prop_db);
        string_ptr player_str = (string_ptr) NULL;

        if (player_no == 1) {
            player_str = UStringMgr_find_string(USTRING_MGR(NuSMVEnv_get_value(env, ENV_STRING_MGR)),PLAYER_NAME_1);
        } else if (player_no == 2) {
            player_str = UStringMgr_find_string(USTRING_MGR(NuSMVEnv_get_value(env, ENV_STRING_MGR)),PLAYER_NAME_2);
        } else {
            nusmv_assert(player_no == 0);
        }

        CATCH(errmgr) {
                PropDbGame_print_all_type_player_status(pdb,
                                                        stdout,
                                                        type,
                                                        player_str,
                                                        status);
            }
        FAIL(errmgr) {
            return 1;
        }
    }

    if (useMore) {
        CmdClosePipe(stdout);
        stdout = old_stdout;
    }
    if (outFileName != NIL(char)) {
        CmdCloseFile(stdout);
        stdout = old_stdout;
        FREE(outFileName);
    }
    return(retval);
}

static int UsageGameShowProperty()
{
    fprintf(stderr,
            "usage: show_property [-h] [-s] [-m | -o output_file]\n" \
    "       [[-n number] |\n" \
    "        [[-u | -t | -f] [-r 1|2] [-a | -A | -d | -D | -b | -l | -g]]]\n");
    fprintf(stderr, "  -h \t\tPrints the command usage.\n");
    fprintf(stderr, "  -s \t\tPrints the number of stored properties.\n");
    fprintf(stderr,
            "  -m \t\tPipes output through the program specified by the \"PAGER\"\n");
    fprintf(stderr,
            "     \t\tenvironment variable if defined, else through UNIX \"more\".\n");
    fprintf(stderr, "  -o file\tWrites the generated output to \"file\".\n");
    fprintf(stderr, "  -u \t\tPrints only unchecked properties.\n");
    fprintf(stderr,
            "  -t \t\tPrints only those properties found to be true.\n");
    fprintf(stderr,
            "  -f \t\tPrints only those properties found to be false.\n");
    fprintf(stderr, "  -a \t\tPrints only REACHTARGET properties.\n");
    fprintf(stderr, "  -A \t\tPrints only AVOIDTARGET properties.\n");
    fprintf(stderr, "  -d \t\tPrints only REACHDEADLOCK properties.\n");
    fprintf(stderr, "  -D \t\tPrints only AVOIDDEADLOCK properties.\n");
    fprintf(stderr, "  -b \t\tPrints only BUCHIGAME properties.\n");
    fprintf(stderr, "  -l \t\tPrints only LTLGAME properties.\n");
    fprintf(stderr, "  -g \t\tPrints only GENREACTIVITY properties.\n");
    return 1;
}

/**Function********************************************************************

  Synopsis           [ Implements the print_usage command. ]

  CommandName        [ print_usage ]

  CommandSynopsis    [ Prints processor and BDD statistics. ]

  CommandArguments   [ \[-h\] ]

  CommandDescription [ Prints a formatted dump of processor-specific
                       usage statistics, and BDD usage statistics. For
                       Berkeley Unix, this includes all of the
                       information in the <tt>getrusage()</tt>
                       structure. <p>

  Command options:<p>
  <dl>
    <dt> <tt>-h</tt>
       <dd> Prints the command usage.
  </dl> ]

  SideEffects        [ ]

  SeeAlso            [ CommandPrintUsage ]

******************************************************************************/
static int CommandGamePrintUsage(NuSMVEnv_ptr env,int argc, char **argv)
{
    int c;
    PropDbGame_ptr pdb;
    PropDb_ptr prop_db  = PROP_DB(NuSMVEnv_get_value(env, ENV_PROP_DB));
    DDMgr_ptr dd_manager = (DDMgr_ptr )NuSMVEnv_get_value(env, ENV_DD_MGR);

    nusmv_assert(opt_game_game(OptsHandler_create()));
    nusmv_assert(opt_cone_of_influence(OptsHandler_create()) == false);

    util_getopt_reset();
    while((c = util_getopt(argc, argv, "h")) != EOF) {
        switch(c) {
            case 'h': return UsageGamePrintUsage();

            default: return UsageGamePrintUsage();
        }
    }

    /* Reporting of statistical information. */
    fprintf(stdout,
            "######################################################################\n");
    util_print_cpu_stats(stdout);
    fprintf(stdout,
            "######################################################################\n");
    fprintf(stdout,
            "BDD statistics\n");
    fprintf(stdout,
            "--------------------\n");
    fprintf(stdout,
            "BDD nodes allocated: %d\n",
            get_dd_nodes_allocated(dd_manager));
    fprintf(stdout,
            "--------------------\n");

    pdb = PROP_DB_GAME(prop_db);
    if (PropDbGame_master_get_game_bdd_fsm(env,pdb) != GAME_BDD_FSM(NULL)) {
        GameBddFsm_print_info(PropDbGame_master_get_game_bdd_fsm(env,pdb), stdout);
    }

    return 0;
}

static int UsageGamePrintUsage()
{
    fprintf(stderr, "usage: print_usage [-h]\n");
    fprintf(stderr, "   -h \t\tPrints the command usage.\n");
    return(1);
}

/**Function********************************************************************

  Synopsis           [ Checks a REACHTARGET game specification. ]

  CommandName        [ check_reach_target ]

  CommandSynopsis    [ ]

  CommandArguments   [ \[-h\] \[-m | -o output-file\] \[-n number\] \[-s\]
                       \[-d\] \[-e\] \[-f strategy-file\] ]

  CommandDescription [ Determines whether a REACHTARGET specification
                       is realizable. If yes, then a strategy for the
                       protagonist may be computed, a counterstrategy
                       for the opponent otherwise. <p>

                       Option <tt>-n</tt> can be used for checking a
                       particular formula in the property
                       database. Otherwise all REACHTARGET
                       specifications in the database are checked. <p>

  Command options:<p>
  <dl>
    <dt> <tt>-h</tt>
       <dd> Prints the command usage.
    <dt> <tt>-m</tt>
       <dd> Pipes the output generated by the command to the program
           specified by the <tt>PAGER</tt> shell variable if defined, else
           through the <tt>UNIX</tt> command "more".
    <dt> <tt>-o output-file</tt>
       <dd> Writes the output generated by the command to the file
           <tt>output-file</tt>.
    <dt> <tt>-n number</tt>
       <dd> Checks the REACHTARGET specification with index <tt>number</tt>
           in the property database.
    <dt> <tt>-s</tt>
       <dd> Requests strategy printing (default to stdout).
    <dt> <tt>-d</tt>
       <dd> Requests strategy printing, generate a DAG (implies -s).
    <dt> <tt>-e</tt>
       <dd> Requests strategy printing, generate an easily readable output
           (implies -s).
    <dt> <tt>-f strategy-file</tt>
       <dd> Writes strategy to "strategy-file" (implies -s).
  </dl><p>

  Strategy printing can also be requested by setting the environment
  variable <tt>game_print_strategy</tt>. ]

  SideEffects        [ ]

  SeeAlso            [ CommandCheck* ]

******************************************************************************/
static int CommandCheckReachTargetSpec(NuSMVEnv_ptr env,int argc, char **argv)
{
    return game_invoke_game_command(env,argc, argv, PropGame_ReachTarget);
}

static int UsageCheckReachTargetSpec()
{
    fprintf(stderr,
            "usage: check_reach_target [-h] [-m | -o output-file] "
                    "[-n number]\n"
                    "       [-s] [-d] [-e] [-f strategy-file]\n");
    fprintf(stderr, "   -h \t\t\tPrints the command usage.\n");
    fprintf(stderr, "   -m \t\t\tPipes output through the program "
            "specified\n");
    fprintf(stderr, "      \t\t\tby the \"PAGER\" environment variable "
            "if defined,\n");
    fprintf(stderr, "      \t\t\telse through the UNIX command \"more\".\n");
    fprintf(stderr, "   -o output-file\tWrites the generated output to "
            "\"output-file\".\n");
    fprintf(stderr, "   -n number\t\tChecks the REACHTARGET specification "
            "with index\n"
            "      \t\t\t\"number\".\n");
    fprintf(stderr, "   -s \t\t\tRequests strategy printing (default to "
            "stdout).\n");
    fprintf(stderr, "   -d \t\t\tRequests strategy printing, generate a DAG "
            "(implies -s).\n");
    fprintf(stderr, "   -e \t\t\tRequests strategy printing, generate an "
            "easily readable\n"
            "      \t\t\toutput (implies -s).\n");
    fprintf(stderr, "   -f strategy-file\tWrites strategy to \"file\" "\
          "(implies -s).\n");
    return 1;
}

/**Function********************************************************************

  Synopsis           [ Checks a AVOIDTARGET game specification. ]

  CommandName        [ check_avoid_target ]

  CommandSynopsis    [ ]

  CommandArguments   [ \[-h\] \[-m | -o output-file\] \[-n number\]
                       \[-a algorithm\] \[-s\] \[-d\] \[-e\]
                       \[-f strategy-file\] ]

  CommandDescription [ Determines whether a AVOIDTARGET specification
                       is realizable. If yes, then a strategy for the
                       protagonist may be computed, a counterstrategy
                       for the opponent otherwise. <p>

                       Option <tt>-n</tt> can be used for checking a
                       particular formula in the property
                       database. Otherwise all AVOIDTARGET
                       specifications in the database are checked. <p>

  Command options:<p>
  <dl>
    <dt> <tt>-h</tt>
       <dd> Prints the command usage.
    <dt> <tt>-m</tt>
       <dd> Pipes the output generated by the command to the program
           specified by the <tt>PAGER</tt> shell variable if defined, else
           through the <tt>UNIX</tt> command "more".
    <dt> <tt>-o output-file</tt>
       <dd> Writes the output generated by the command to the file
           <tt>output-file</tt>.
    <dt> <tt>-n number</tt>
       <dd> Checks the AVOIDTARGET specification with index <tt>number</tt>
           in the property database.
    <dt> <tt>-a algorithm</tt>
       <dd> Uses algorithm <tt>algorithm</tt>. Available algorithms are:
           <tt>default</tt>.
    <dt> <tt>-s</tt>
       <dd> Requests strategy printing (default to stdout).
    <dt> <tt>-d</tt>
       <dd> Requests strategy printing, generate a DAG (implies -s).
    <dt> <tt>-e</tt>
       <dd> Requests strategy printing, generate an easily readable output
           (implies -s).
    <dt> <tt>-f strategy-file</tt>
       <dd> Writes strategy to "strategy-file" (implies -s).
  </dl><p>

  Strategy printing can also be requested by setting the environment
  variable <tt>game_print_strategy</tt>. ]

  SideEffects        [ ]

  SeeAlso            [ CommandCheck* ]

******************************************************************************/
static int CommandCheckAvoidTargetSpec(NuSMVEnv_ptr env,int argc, char **argv)
{
    return game_invoke_game_command(env,argc, argv, PropGame_AvoidTarget);
}

static int UsageCheckAvoidTargetSpec()
{
    fprintf(stderr,
            "usage: check_avoid_target [-h] [-m | -o output-file] "
                    "[-n number] [-a algorithm]\n"
                    "       [-s] [-d] [-e] [-f strategy-file]\n");
    fprintf(stderr, "   -h \t\t\tPrints the command usage.\n");
    fprintf(stderr, "   -m \t\t\tPipes output through the program "
            "specified\n");
    fprintf(stderr, "      \t\t\tby the \"PAGER\" environment variable "
            "if defined,\n");
    fprintf(stderr, "      \t\t\telse through the UNIX command \"more\".\n");
    fprintf(stderr, "   -o output-file\tWrites the generated output to "
            "\"output-file\".\n");
    fprintf(stderr, "   -n number\t\tChecks the AVOIDTARGET specification "
            "with index\n"
            "      \t\t\t\"number\".\n");
    fprintf(stderr, "   -a algorithm\t\tUses algorithm \"algorithm\". "
            "Available algorithms\n"
            "      \t\t\tare: default.\n");
    fprintf(stderr, "   -s \t\t\tRequests strategy printing (default to "
            "stdout).\n");
    fprintf(stderr, "   -d \t\t\tRequests strategy printing, generate a DAG "
            "(implies -s).\n");
    fprintf(stderr, "   -e \t\t\tRequests strategy printing, generate an "
            "easily readable\n"
            "      \t\t\toutput (implies -s).\n");
    fprintf(stderr, "   -f strategy-file\tWrites strategy to \"file\" "\
          "(implies -s).\n");
    return 1;
}

/**Function********************************************************************

  Synopsis           [ Checks a REACHDEADLOCK game specification. ]

  CommandName        [ check_reach_deadlock ]

  CommandSynopsis    [ ]

  CommandArguments   [ \[-h\] \[-m | -o output-file\] \[-n number\] \[-s\]
                       \[-d\] \[-e\] \[-f strategy-file\] ]

  CommandDescription [ Determines whether a REACHDEADLOCK
                       specification is realizable. If yes, then a
                       strategy for the protagonist may be computed, a
                       counterstrategy for the opponent otherwise. <p>

                       Option <tt>-n</tt> can be used for checking a
                       particular formula in the property
                       database. Otherwise all REACHDEADLOCK
                       specifications in the database are checked. <p>

  Command options:<p>
  <dl>
    <dt> <tt>-h</tt>
       <dd> Prints the command usage.
    <dt> <tt>-m</tt>
       <dd> Pipes the output generated by the command to the program
           specified by the <tt>PAGER</tt> shell variable if defined, else
           through the <tt>UNIX</tt> command "more".
    <dt> <tt>-o output-file</tt>
       <dd> Writes the output generated by the command to the file
           <tt>output-file</tt>.
    <dt> <tt>-n number</tt>
       <dd> Checks the REACHDEADLOCK specification with index <tt>number</tt>
           in the property database.
    <dt> <tt>-s</tt>
       <dd> Requests strategy printing (default to stdout).
    <dt> <tt>-d</tt>
       <dd> Requests strategy printing, generate a DAG (implies -s).
    <dt> <tt>-e</tt>
       <dd> Requests strategy printing, generate an easily readable output
           (implies -s).
    <dt> <tt>-f strategy-file</tt>
       <dd> Writes strategy to "strategy-file" (implies -s).
  </dl><p>

  Strategy printing can also be requested by setting the environment
  variable <tt>game_print_strategy</tt>. ]

  SideEffects        [ ]

  SeeAlso            [ CommandCheck* ]

******************************************************************************/
static int CommandCheckReachDeadlockSpec(NuSMVEnv_ptr env,int argc, char **argv)
{
    return game_invoke_game_command(env,argc, argv, PropGame_ReachDeadlock);
}

static int UsageCheckReachDeadlockSpec()
{
    fprintf(stderr,
            "usage: check_reach_deadlock [-h] [-m | -o output-file] "
                    "[-n number]\n"
                    "       [-s] [-d] [-e] [-f strategy-file]\n");
    fprintf(stderr, "   -h \t\t\tPrints the command usage.\n");
    fprintf(stderr, "   -m \t\t\tPipes output through the program "
            "specified\n");
    fprintf(stderr, "      \t\t\tby the \"PAGER\" environment variable "
            "if defined,\n");
    fprintf(stderr, "      \t\t\telse through the UNIX command \"more\".\n");
    fprintf(stderr, "   -o output-file\tWrites the generated output to "
            "\"output-file\".\n");
    fprintf(stderr, "   -n number\t\tChecks the REACHDEADLOCK specification "
            "with index\n"
            "      \t\t\t\"number\".\n");
    fprintf(stderr, "   -s \t\t\tRequests strategy printing (default to "
            "stdout).\n");
    fprintf(stderr, "   -d \t\t\tRequests strategy printing, generate a DAG "
            "(implies -s).\n");
    fprintf(stderr, "   -e \t\t\tRequests strategy printing, generate an "
            "easily readable\n"
            "      \t\t\toutput (implies -s).\n");
    fprintf(stderr, "   -f strategy-file\tWrites strategy to \"file\" "\
          "(implies -s).\n");
    return 1;
}

/**Function********************************************************************

  Synopsis           [ Checks a AVOIDDEADLOCK game specification. ]

  CommandName        [ check_avoid_deadlock ]

  CommandSynopsis    [ ]

  CommandArguments   [ \[-h\] \[-m | -o output-file\] \[-n number\] \[-s\]
                       \[-d\] \[-e\] \[-f strategy-file\] ]

  CommandDescription [ Determines whether a AVOIDDEADLOCK
                       specification is realizable. If yes, then a
                       strategy for the protagonist may be computed, a
                       counterstrategy for the opponent otherwise. <p>

                       Option <tt>-n</tt> can be used for checking a
                       particular formula in the property
                       database. Otherwise all AVOIDDEADLOCK
                       specifications in the database are checked. <p>

  Command options:<p>
  <dl>
    <dt> <tt>-h</tt>
       <dd> Prints the command usage.
    <dt> <tt>-m</tt>
       <dd> Pipes the output generated by the command to the program
           specified by the <tt>PAGER</tt> shell variable if defined, else
           through the <tt>UNIX</tt> command "more".
    <dt> <tt>-o output-file</tt>
       <dd> Writes the output generated by the command to the file
           <tt>output-file</tt>.
    <dt> <tt>-n number</tt>
       <dd> Checks the AVOIDDEADLOCK specification with index <tt>number</tt>
           in the property database.
    <dt> <tt>-s</tt>
       <dd> Requests strategy printing (default to stdout).
    <dt> <tt>-d</tt>
       <dd> Requests strategy printing, generate a DAG (implies -s).
    <dt> <tt>-e</tt>
       <dd> Requests strategy printing, generate an easily readable output
           (implies -s).
    <dt> <tt>-f strategy-file</tt>
       <dd> Writes strategy to "strategy-file" (implies -s).
  </dl><p>

  Strategy printing can also be requested by setting the environment
  variable <tt>game_print_strategy</tt>. ]

  SideEffects        [ ]

  SeeAlso            [ CommandCheck* ]

******************************************************************************/
static int CommandCheckAvoidDeadlockSpec(NuSMVEnv_ptr env,int argc, char **argv)
{
    return game_invoke_game_command(env,argc, argv, PropGame_AvoidDeadlock);
}

static int UsageCheckAvoidDeadlockSpec()
{
    fprintf(stderr,
            "usage: check_avoid_deadlock [-h] [-m | -o output-file] "
                    "[-n number]\n"
                    "       [-s] [-d] [-e] [-f strategy-file]\n");
    fprintf(stderr, "   -h \t\t\tPrints the command usage.\n");
    fprintf(stderr, "   -m \t\t\tPipes output through the program "
            "specified\n");
    fprintf(stderr, "      \t\t\tby the \"PAGER\" environment variable "
            "if defined,\n");
    fprintf(stderr, "      \t\t\telse through the UNIX command \"more\".\n");
    fprintf(stderr, "   -o output-file\tWrites the generated output to "
            "\"output-file\".\n");
    fprintf(stderr, "   -n number\t\tChecks the AVOIDDEADLOCK specification "
            "with index\n"
            "      \t\t\t\"number\".\n");
    fprintf(stderr, "   -s \t\t\tRequests strategy printing (default to "
            "stdout).\n");
    fprintf(stderr, "   -d \t\t\tRequests strategy printing, generate a DAG "
            "(implies -s).\n");
    fprintf(stderr, "   -e \t\t\tRequests strategy printing, generate an "
            "easily readable\n"
            "      \t\t\toutput (implies -s).\n");
    fprintf(stderr, "   -f strategy-file\tWrites strategy to \"file\" "\
          "(implies -s).\n");
    return 1;
}

/**Function********************************************************************

  Synopsis           [ Checks a BUCHIGAME game specification. ]

  CommandName        [ check_buchi_game ]

  CommandSynopsis    [ ]

  CommandArguments   [ \[-h\] \[-m | -o output-file\] \[-n number\] \[-s\]
                       \[-d\] \[-e\] \[-f strategy-file\] ]

  CommandDescription [ Determines whether a BUCHIGAME specification
                       is realizable. If yes, then a strategy for the
                       protagonist may be computed, a counterstrategy
                       for the opponent otherwise. <p>

                       Option <tt>-n</tt> can be used for checking a
                       particular formula in the property
                       database. Otherwise all BUCHIGAME
                       specifications in the database are checked. <p>

  Command options:<p>
  <dl>
    <dt> <tt>-h</tt>
       <dd> Prints the command usage.
    <dt> <tt>-m</tt>
       <dd> Pipes the output generated by the command to the program
           specified by the <tt>PAGER</tt> shell variable if defined, else
           through the <tt>UNIX</tt> command "more".
    <dt> <tt>-o output-file</tt>
       <dd> Writes the output generated by the command to the file
           <tt>output-file</tt>.
    <dt> <tt>-n number</tt>
       <dd> Checks the BUCHIGAME specification with index <tt>number</tt>
           in the property database.
    <dt> <tt>-s</tt>
       <dd> Requests strategy printing (default to stdout).
    <dt> <tt>-d</tt>
       <dd> Requests strategy printing, generate a DAG (implies -s).
    <dt> <tt>-e</tt>
       <dd> Requests strategy printing, generate an easily readable output
           (implies -s).
    <dt> <tt>-f strategy-file</tt>
       <dd> Writes strategy to "strategy-file" (implies -s).
  </dl><p>

  Strategy printing can also be requested by setting the environment
  variable <tt>game_print_strategy</tt>. ]

  SideEffects        [ ]

  SeeAlso            [ CommandCheck* ]

******************************************************************************/
static int CommandCheckBuchiGameSpec(NuSMVEnv_ptr env,int argc, char **argv)
{
    return game_invoke_game_command(env,argc, argv, PropGame_BuchiGame);
}

static int UsageCheckBuchiGameSpec()
{
    fprintf(stderr,
            "usage: check_buchi_game [-h] [-m | -o output-file] "
                    "[-n number]\n"
                    "       [-s] [-d] [-e] [-f strategy-file]\n");
    fprintf(stderr, "   -h \t\t\tPrints the command usage.\n");
    fprintf(stderr, "   -m \t\t\tPipes output through the program "
            "specified\n");
    fprintf(stderr, "      \t\t\tby the \"PAGER\" environment variable "
            "if defined,\n");
    fprintf(stderr, "      \t\t\telse through the UNIX command \"more\".\n");
    fprintf(stderr, "   -o output-file\tWrites the generated output to "
            "\"output-file\".\n");
    fprintf(stderr, "   -n number\t\tChecks the BUCHIGAME specification "
            "with index\n"
            "      \t\t\t\"number\".\n");
    fprintf(stderr, "   -s \t\t\tRequests strategy printing (default to "
            "stdout).\n");
    fprintf(stderr, "   -d \t\t\tRequests strategy printing, generate a DAG "
            "(implies -s).\n");
    fprintf(stderr, "   -e \t\t\tRequests strategy printing, generate an "
            "easily readable\n"
            "      \t\t\toutput (implies -s).\n");
    fprintf(stderr, "   -f strategy-file\tWrites strategy to \"file\" "\
          "(implies -s).\n");
    return 1;
}

/**Function********************************************************************

  Synopsis           [ Checks a GENREACTIVITY game specification. ]

  CommandName        [ check_gen_reactivity ]

  CommandSynopsis    [ ]

  CommandArguments   [ \[-h\] \[-m | -o output-file\] \[-n number\] \[-s\]
                       \[-d\] \[-e\] \[-f strategy-file\] ]

  CommandDescription [ Determines whether a GENREACTIVITY specification
                       is realizable. If yes, then a strategy for the
                       protagonist may be computed, a counterstrategy
                       for the opponent otherwise. <p>

                       Option <tt>-n</tt> can be used for checking a
                       particular formula in the property
                       database. Otherwise all GENREACTIVITY
                       specifications in the database are checked. <p>

  Command options:<p>
  <dl>
    <dt> <tt>-h</tt>
       <dd> Prints the command usage.
    <dt> <tt>-m</tt>
       <dd> Pipes the output generated by the command to the program
           specified by the <tt>PAGER</tt> shell variable if defined, else
           through the <tt>UNIX</tt> command "more".
    <dt> <tt>-o output-file</tt>
       <dd> Writes the output generated by the command to the file
           <tt>output-file</tt>.
    <dt> <tt>-n number</tt>
       <dd> Checks the GENREACTIVITY specification with index <tt>number</tt>
           in the property database.
    <dt> <tt>-s</tt>
       <dd> Requests strategy printing (default to stdout).
    <dt> <tt>-d</tt>
       <dd> Requests strategy printing, generate a DAG (implies -s).
    <dt> <tt>-e</tt>
       <dd> Requests strategy printing, generate an easily readable output
           (implies -s).
    <dt> <tt>-f strategy-file</tt>
       <dd> Writes strategy to "strategy-file" (implies -s).
  </dl><p>

  Strategy printing can also be requested by setting the environment
  variable <tt>game_print_strategy</tt>. ]

  SideEffects        [ ]

  SeeAlso            [ CommandCheck* ]

******************************************************************************/
static int CommandCheckGenReactivitySpec(NuSMVEnv_ptr env,int argc, char **argv)
{
    return game_invoke_game_command(env,argc, argv, PropGame_GenReactivity);
}

static int UsageCheckGenReactivitySpec()
{
    fprintf(stderr,
            "usage: check_gen_reactivity [-h] [-m | -o output-file] "
                    "[-n number]\n"
                    "       [-s] [-d] [-e] [-f strategy-file]\n");
    fprintf(stderr, "   -h \t\t\tPrints the command usage.\n");
    fprintf(stderr, "   -m \t\t\tPipes output through the program "
            "specified\n");
    fprintf(stderr, "      \t\t\tby the \"PAGER\" environment variable "
            "if defined,\n");
    fprintf(stderr, "      \t\t\telse through the UNIX command \"more\".\n");
    fprintf(stderr, "   -o output-file\tWrites the generated output to "
            "\"output-file\".\n");
    fprintf(stderr, "   -n number\t\tChecks the GENREACTIVITY specification "
            "with index\n"
            "      \t\t\t\"number\".\n");
    fprintf(stderr, "   -s \t\t\tRequests strategy printing (default to "
            "stdout).\n");
    fprintf(stderr, "   -d \t\t\tRequests strategy printing, generate a DAG "
            "(implies -s).\n");
    fprintf(stderr, "   -e \t\t\tRequests strategy printing, generate an "
            "easily readable\n"
            "      \t\t\toutput (implies -s).\n");
    fprintf(stderr, "   -f strategy-file\tWrites strategy to \"file\" "\
          "(implies -s).\n");
    return 1;
}

/**Function********************************************************************

  Synopsis    [ Actual command processing for CommandCheckReachTarget,
                CommandCheckAvoidTarget, CommandCheckReachDeadlock,
                CommandCheckAvoidDeadlock, CommandCheckBuchiGame,
                CommandCheckGenReactivity. ]

  Description [ For details see the documentation of the respective
                CommandCheck* functions. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
static int game_invoke_game_command(NuSMVEnv_ptr env,int argc, char **argv, PropGame_Type type)
{
    int c;
    int res;
    int prop_no = -1;
    int useMore = 0;
    int strategy_printout = 0;
    int indented_printout = 0;
    int strategy_printout_as_dag = 0;
    char* dbgFileName = NIL(char);
    char* strategyFileName = NIL(char);
    FILE* old_stdout = (FILE*) NULL;
    FILE* strategy_stream =(FILE*) NULL;
    char* algorithm = NIL(char);
    PropDb_ptr prop_db  = PROP_DB(NuSMVEnv_get_value(env, ENV_PROP_DB));

    /* command related parameters */
    command_function_ptr command_function;
    int (*command_usage)(void);
    char* command_options;
    ErrorMgr_ptr const errmgr =
            ERROR_MGR(NuSMVEnv_get_value(env, ENV_ERROR_MANAGER));

    nusmv_assert(opt_game_game(OptsHandler_create()));

    switch(type) {
        case PropGame_ReachTarget:
            command_function = Game_CheckReachTargetSpec;
            command_usage = UsageCheckReachTargetSpec;
            command_options = "hmo:n:sf:de";
            break;
        case PropGame_ReachDeadlock:
            command_function = Game_CheckReachDeadlockSpec;
            command_usage = UsageCheckReachDeadlockSpec;
            command_options = "hmo:n:sf:de";
            break;
        case PropGame_AvoidTarget:
            command_function = Game_CheckAvoidTargetSpec;
            command_usage = UsageCheckAvoidTargetSpec;
            command_options = "ha:mo:n:sf:de";
            break;
        case PropGame_AvoidDeadlock:
            command_function = Game_CheckAvoidDeadlockSpec;
            command_usage = UsageCheckAvoidDeadlockSpec;
            command_options = "hmo:n:sf:de";
            break;
        case PropGame_BuchiGame:
            command_function = Game_CheckBuchiGameSpec;
            command_usage = UsageCheckBuchiGameSpec;
            command_options = "hmo:n:sf:de";
            break;
        case PropGame_GenReactivity:
            command_function = Game_CheckGenReactivitySpec;
            command_usage = UsageCheckGenReactivitySpec;
            command_options = "hmo:n:sf:de";
            break;
        default: nusmv_assert(false); /* illegal command's kind */
    }

    /*  --------  EVALUATING THE OPTIONS OF THE COMMAND --------- */
    util_getopt_reset();
    while ((c = util_getopt(argc, argv, command_options)) != EOF) {
        switch (c) {
            case 'h':
                goto game_invoke_game_command_return_usage;

            case 'm':
                if (useMore == 1) goto game_invoke_game_command_return_usage;
                if (dbgFileName != NIL(char)) goto game_invoke_game_command_return_usage;
                useMore = 1;
                break;

            case 'o':
                if (dbgFileName != NIL(char)) goto game_invoke_game_command_return_usage;
                if (useMore == 1) goto game_invoke_game_command_return_usage;
                dbgFileName = util_strsav(util_optarg);
                fprintf(stdout, "Output to file: %s\n", dbgFileName);
                break;

            case 'n':
                if (prop_no != -1) goto game_invoke_game_command_return_usage;
                prop_no = PropDb_get_prop_index_from_string(prop_db,
                                                            util_optarg);
                if (prop_no == -1) goto game_invoke_game_command_return_1;
                break;

            case 'a':
                if (algorithm != NULL) goto game_invoke_game_command_return_usage;
                algorithm = util_strsav(util_optarg);

                switch (type) { /* check the name of an algorithm */
                    case PropGame_AvoidTarget:
                        if (strcmp("default", algorithm) == 0) {
                            /* do not reset checking function */
                        }
                        else goto game_invoke_game_command_return_usage;
                        break;

                    default:
                        nusmv_assert(false);
                }
                break;

            case 's':
                strategy_printout = 1;
                break;

            case 'd':
                /* -d implies -s */
                strategy_printout = 1;
                strategy_printout_as_dag = 1;
                break;

            case 'e':
                /* -e implies -s */
                strategy_printout = 1;
                indented_printout = 1;
                break;

            case 'f':
                if (strategyFileName != NIL(char)) {
                    goto game_invoke_game_command_return_usage;
                }
                strategyFileName = util_strsav(util_optarg);
                /* -f implies -s */
                strategy_printout = 1;
                break;

            default:
                goto game_invoke_game_command_return_usage;
        }
    }
    if (argc != util_optind) goto game_invoke_game_command_return_usage;

    /* This command is only available in game mode. That means that a
       game model has been read. If this statement becomes false at some
       point, then insert a check for having read a model here. */

    if (Compile_check_if_encoding_was_built(env,stderr)) {
        goto game_invoke_game_command_return_1;
    }

    if (Compile_check_if_model_was_built(env,stderr, false)) {
        goto game_invoke_game_command_return_1;
    }

    if (useMore) {
        old_stdout = stdout;
        stdout = CmdOpenPipe(env,useMore);
        if (stdout == (FILE*) NULL) {
            goto game_invoke_game_command_return_1;
        }
    }

    if (dbgFileName != NIL(char)) {
        old_stdout = stdout;
        stdout = CmdOpenFile(env,dbgFileName);
        if (stdout == (FILE*) NULL) {
            goto game_invoke_game_command_return_1;
        }
    }

    if (NIL(char) != strategyFileName) {
        strategy_stream = CmdOpenFile(env,strategyFileName);
        if (strategy_stream == (FILE*) NULL) {
            goto game_invoke_game_command_return_1;
        }
    }

    if (strategy_printout) {
        fprintf(stdout,
                "%s strategy printout enabled (out -> %s, indentation is %s)\n",
                (strategy_printout_as_dag ? "dag" : "flat"),
                (NIL(char) != strategyFileName ? strategyFileName : "<stdout>"),
                (indented_printout ? "enabled" : "disabled"));
    }

    /* --------- CHECKING THE FORMULA -------------------*/

    /* The formula is specified. */
    if (prop_no != -1) {
        Prop_ptr p = PropDb_get_prop_at_index(prop_db, prop_no);

        /* Check its kind. */
        if (Prop_check_type(p, type) != 0) {
            goto game_invoke_game_command_return_1;
        }

        CATCH(errmgr) {
                GameParams params;
                params.strategy_printout = strategy_printout;
                params.printout_as_dag   = strategy_printout_as_dag;
                params.indented_printout = indented_printout;
                params.strategy_stream   = strategy_stream;

                /* strategyFileName == NULL <-> strategy_stream == NULL */
                nusmv_assert(((strategyFileName == NIL(char)) &&
                             (strategy_stream == (FILE*) NULL)) ||
                             ((strategyFileName != NIL(char)) &&
                             (strategy_stream != (FILE*) NULL)));
                command_function(env,PROP_GAME(p), &params);
            }
        FAIL(errmgr) {
            goto game_invoke_game_command_return_1;
        }
    }
        /* (probably many) formulas are specified. check them all */
    else {
        CATCH(errmgr) {
                int i;
                int s = PropDb_get_size(prop_db);

                GameParams params;
                params.strategy_printout = strategy_printout;
                params.printout_as_dag   = strategy_printout_as_dag;
                params.indented_printout = indented_printout;
                params.strategy_stream   = strategy_stream;

                /* strategyFileName == NULL <-> strategy_stream == NULL */
                nusmv_assert(((strategyFileName == NIL(char)) &&
                             (strategy_stream == (FILE*) NULL)) ||
                             ((strategyFileName != NIL(char)) &&
                             (strategy_stream != (FILE*) NULL)));
                for (i=0; i < s; ++i) {
                    Prop_ptr p = PropDb_get_prop_at_index(prop_db, i);

                    if (Prop_get_type(p) == type) {
                        command_function(env,PROP_GAME(p), &params);
                    }
                }
            }
        FAIL(errmgr) {
            goto game_invoke_game_command_return_1;
        }
    }

    res = 0;
    goto game_invoke_game_command_cleanup_and_return;

    game_invoke_game_command_return_1:
    res = 1;
    goto game_invoke_game_command_cleanup_and_return;

    game_invoke_game_command_return_usage:
    res = -1;
    goto game_invoke_game_command_cleanup_and_return;

    game_invoke_game_command_cleanup_and_return:
    if (useMore) {
        if (stdout != (FILE*) NULL) CmdClosePipe(stdout);
        stdout = old_stdout;
    }
    if (dbgFileName != NIL(char)) {
        if (stdout != (FILE*) NULL) CmdCloseFile(stdout);
        stdout = old_stdout;
        FREE(dbgFileName);
    }
    if (algorithm != NIL(char)) {
        FREE(algorithm);
    }
    if (strategyFileName != NIL(char)) {
        if (strategy_stream != (FILE*) NULL) CmdCloseFile(strategy_stream);
        FREE(strategyFileName);
    }

    switch(res) {
        case 0:
            /* fall through */
        case 1:
            return res;
        case -1:
            return command_usage();
        default:
            nusmv_assert(false);
    }
}

/**Function********************************************************************

  Synopsis           [ Checks an LTLGAME specification using the sf07
                       algorithm. ]

  CommandName        [ check_ltlgame_sf07 ]

  CommandSynopsis    [ Checks an LTLGAME specification using the sf07
                       algorithm. ]

  CommandArguments   [ \[-h\] \[-m | -o output-file\] \[-n number\]
                       \[-s\] \[-d\] \[-e\] \[-f strategy-file\]
                       \[-k number\] \[-K number\] \[-w p|a|b|1|2\] ]

  CommandDescription [ Determines whether an LTLGAME specification is
                       realizable using the sf07 algorithm. If yes,
                       then a strategy for the protagonist may be
                       computed, a counterstrategy for the opponent
                       otherwise. <p>

                       Option <tt>-n</tt> can be used for checking a
                       particular formula in the property
                       database. Otherwise all LTLGAME
                       specifications in the database are checked. <p>

  Command options:<p>
  <dl>
    <dt> <tt>-h</tt>
       <dd> Prints the command usage.
    <dt> <tt>-m</tt>
       <dd> Pipes the output generated by the command to the program
           specified by the <tt>PAGER</tt> shell variable if defined, else
           through the <tt>UNIX</tt> command "more".
    <dt> <tt>-o output-file</tt>
       <dd> Writes the output generated by the command to the file
           <tt>output-file</tt>.
    <dt> <tt>-n number</tt>
       <dd> Checks the LTLGAME specification with index <tt>number</tt>
           in the property database.
    <dt> <tt>-s</tt>
       <dd> Requests strategy printing (default to stdout).
    <dt> <tt>-d</tt>
       <dd> Requests strategy printing, generate a DAG (implies -s).
    <dt> <tt>-e</tt>
       <dd> Requests strategy printing, generate an easily readable output
           (implies -s).
    <dt> <tt>-f strategy-file</tt>
       <dd> Writes strategy to "strategy-file" (implies -s).
    <dt> <tt>-k number</tt>
       <dd> Start value for k (default 0).
    <dt> <tt>-K number</tt>
       <dd> End value for k (default 20).
    <dt> <tt>-w p|a|b|1|2</tt>
       <dd> Whom games are played for: (p)rotagonist, (a)ntagonist, (b)oth,
           player (1), or player (2). Default: b.
  </dl><p>

  Strategy printing can also be requested by setting the environment
  variable <tt>game_print_strategy</tt>. <p>

  Further relevant environment variables are:
  <dl>
    <dt> <tt>game_sf07_gba_wring_binary</tt>
       <dd> Specifies the path to the LTL to B&uuml;chi translator.
    <dt> <tt>game_sf07_gba_wring_has_cc</tt>
       <dd> Specifies whether the LTL to B&uuml;chi translator has the option
           <tt>-cc</tt> to degeneralize the resulting automaton (this
           implementation requires simple automata).
    <dt> <tt>game_sf07_gba_wring_input_dir</tt>
       <dd> Directory to store input files to the LTL to B&uuml;chi translator.
    <dt> <tt>game_sf07_gba_wring_input_templ</tt>
       <dd> Template for filenames of input files to the LTL to B&uuml;chi
           translator.
    <dt> <tt>game_sf07_gba_wring_input_keep</tt>
       <dd> Whether input files to the LTL to B&uuml;chi translator should be
           kept or removed.
    <dt> <tt>game_sf07_gba_wring_output_dir</tt>
       <dd> Directory to store output files of the LTL to B&uuml;chi translator.
    <dt> <tt>game_sf07_gba_wring_output_templ</tt>
       <dd> Template for filenames of output files of the LTL to B&uuml;chi
           translator.
    <dt> <tt>game_sf07_gba_wring_output_keep</tt>
       <dd> Whether output files of the LTL to B&uuml;chi translator should be
           kept or removed.
    <dt> <tt>game_sf07_strategy_printing_mode</tt>
       <dd> Whether the monitor part of a winning stratey should be printed
           from its original sexp, from its BDD FSM, or from its BDD FSM after
           conjunction with the winning strategy in the subgame.
  </dl><p> ]

  SideEffects        [ ]

  SeeAlso            [ CommandCheck* ]

******************************************************************************/
static int CommandCheckLtlGameSpecSF07(NuSMVEnv_ptr env,int argc, char **argv)
{
    int c;
    int prop_no = -1;
    int status;
    int useMore = 0;
    int strategy_printout = 0;
    int indented_printout = 0;
    int strategy_printout_as_dag = 0;
    char* dbgFileName = NIL(char);
    char* strategyFileName = NIL(char);
    FILE* old_stdout = (FILE*) NULL;
    FILE* strategy_stream =(FILE*) NULL;
    int kmin = -1;
    int kmax = -1;
    Game_Who w = GAME_WHO_INVALID;

    const ErrorMgr_ptr errmgr = ERROR_MGR(NuSMVEnv_get_value(env, ENV_ERROR_MANAGER));

    PropDb_ptr prop_db  = PROP_DB(NuSMVEnv_get_value(env, ENV_PROP_DB));

    nusmv_assert(opt_game_game(OptsHandler_create()));

    /*  --------  EVALUATING THE OPTIONS OF THE COMMAND --------- */
    util_getopt_reset();
    while ((c = util_getopt(argc, argv, "hmo:n:sf:dek:K:w:")) != EOF) {
        switch (c) {
            case 'h': goto CommandCheckLtlGameSpecSF07_return_usage;
            case 'm':
                if (dbgFileName != NIL(char)) {
                    goto CommandCheckLtlGameSpecSF07_return_usage;
                }
                useMore = 1;
                break;
            case 'o':
                if (useMore == 1) { goto CommandCheckLtlGameSpecSF07_return_usage; }
                dbgFileName = util_strsav(util_optarg);
                fprintf(stdout, "Output to file: %s\n", dbgFileName);
                break;
            case 'n':
                if (prop_no != -1) { goto CommandCheckLtlGameSpecSF07_return_usage; }
                prop_no = PropDb_get_prop_index_from_string(prop_db,
                                                            util_optarg);
                if (prop_no == -1) { goto CommandCheckLtlGameSpecSF07_return_1; }
                break;
            case 's':
                strategy_printout = 1;
                break;
            case 'f':
                strategyFileName = util_strsav(util_optarg);
                /* -f implies -s */
                strategy_printout = 1;
                break;
            case 'd':
                strategy_printout_as_dag = 1;
                /* -d implies -s */
                strategy_printout = 1;
                break;
            case 'e':
                indented_printout = 1;
                /* -e implies -s */
                strategy_printout = 1;
                break;
            case 'k':
            {
                char* strNumber;
                if (kmin != -1) { goto CommandCheckLtlGameSpecSF07_return_usage; }
                strNumber = util_strsav(util_optarg);
                if (util_str2int(strNumber, &kmin) != 0) {
                    FREE(strNumber);
                    goto CommandCheckLtlGameSpecSF07_return_usage;
                }
                if (kmin<0) {
                    FREE(strNumber);
                    goto CommandCheckLtlGameSpecSF07_return_usage;
                }
                FREE(strNumber);
            }
                break;
            case 'K':
            {
                char* strNumber;
                if (kmax != -1) { goto CommandCheckLtlGameSpecSF07_return_usage; }
                strNumber = util_strsav(util_optarg);
                if (util_str2int(strNumber, &kmax) != 0) {
                    FREE(strNumber);
                    goto CommandCheckLtlGameSpecSF07_return_usage;
                }
                if (kmax<0) {
                    FREE(strNumber);
                    goto CommandCheckLtlGameSpecSF07_return_usage;
                }
                FREE(strNumber);
            }
                break;
            case 'w':
            {
                char* strWhom;
                if (w != GAME_WHO_INVALID) {
                    goto CommandCheckLtlGameSpecSF07_return_usage;
                }
                strWhom = util_strsav(util_optarg);
                w = Game_Who_from_string(strWhom);
                if (w != GAME_WHO_PROTAGONIST &&
                    w != GAME_WHO_ANTAGONIST &&
                    w != GAME_WHO_BOTH &&
                    w != GAME_WHO_PLAYER_1 &&
                    w != GAME_WHO_PLAYER_2) {
                    FREE(strWhom);
                    goto CommandCheckLtlGameSpecSF07_return_usage;
                }
                FREE(strWhom);
            }
                break;
            default: goto CommandCheckLtlGameSpecSF07_return_usage;
        }
    }

    if (argc != util_optind) { goto CommandCheckLtlGameSpecSF07_return_usage; }

    /* This command is only available in game mode. That means that a
       game model has been read. If this statement becomes false at some
       point, then insert a check for having read a model here. */

    if (Compile_check_if_encoding_was_built(env,stderr)) {
        goto CommandCheckLtlGameSpecSF07_return_1;
    }

    if (Compile_check_if_model_was_built(env,stderr, false)) {
        goto CommandCheckLtlGameSpecSF07_return_1;
    }

    if (Compile_check_if_bool_model_was_built(env,stderr, false)) {
        goto CommandCheckLtlGameSpecSF07_return_1;
    }

    if (opt_game_game_initial_condition(OptsHandler_create()) != 'N') {
        fprintf(stderr,
                "Command check_ltlgame_sf07 only supports \'N\' as initial game "
                        "condition.\n");
    }

    if (useMore) {
        old_stdout = stdout;
        stdout = CmdOpenPipe(env,useMore);
        if (stdout==(FILE*) NULL) {
            stdout=old_stdout;
            old_stdout = (FILE*) NULL;
            goto CommandCheckLtlGameSpecSF07_return_1;
        }
    }

    if (dbgFileName != NIL(char)) {
        old_stdout = stdout;
        stdout = CmdOpenFile(env,dbgFileName);
        if (stdout==(FILE*) NULL) {
            stdout = old_stdout;
            old_stdout = (FILE*) NULL;
            goto CommandCheckLtlGameSpecSF07_return_1;
        }
    }

    if (NIL(char) != strategyFileName) {
        strategy_stream = CmdOpenFile(env,strategyFileName);
        if ((FILE*) NULL == strategy_stream) {
            goto CommandCheckLtlGameSpecSF07_return_1;
        }
    }

    if (kmin == -1) { kmin = DEFAULT_GAME_CHECK_LTL_GAME_SPEC_SF07_KMIN; }
    if (kmax == -1) { kmax = DEFAULT_GAME_CHECK_LTL_GAME_SPEC_SF07_KMAX; }
    if (kmax < kmin) { goto CommandCheckLtlGameSpecSF07_return_usage; }

    if (w == GAME_WHO_INVALID) { w = DEFAULT_GAME_CHECK_LTL_GAME_SPEC_SF07_W; }

    if (strategy_printout) {
        fprintf(
                stdout,
                "%s strategy printout enabled (out -> %s, indentation is %s)\n",

                strategy_printout_as_dag
                ? "dag"
                : "flat",

                NIL(char) != strategyFileName
                ? strategyFileName
                : "<stdout>",

                indented_printout
                ? "enabled"
                : "disabled");
    }

    /* --------- CHECKING THE FORMULA -------------------*/

    /* the formula is specified. check its kind */
    if (prop_no != -1) {
        if (Prop_check_type(PropDb_get_prop_at_index(prop_db,
                                                     prop_no),
                            PropGame_LtlGame) != 0) {
            goto CommandCheckLtlGameSpecSF07_return_1;
        }
    }

    /* one formula is specified. check it alone */
    if (prop_no != -1) {
        CATCH(errmgr) {
                Prop_ptr p = PropDb_get_prop_at_index(prop_db,
                                                      prop_no);
                nusmv_assert(Prop_get_type(p) == PropGame_LtlGame);

                GameParams params;
                params.strategy_printout = strategy_printout;
                params.printout_as_dag = strategy_printout_as_dag;
                params.indented_printout = indented_printout;
                params.strategy_stream = strategy_stream;

                /* strategyFileName == NULL <-> strategy_stream == NULL */
                nusmv_assert(
                        (NIL(char) != strategyFileName ||
                (FILE*) NULL == strategy_stream) &&
                (NIL(char) == strategyFileName ||
                (FILE*) NULL != strategy_stream) );

                Game_CheckLtlGameSpecSF07(env,PROP_GAME(p), &params, kmin, kmax, w);
            }
        FAIL(errmgr) {
            goto CommandCheckLtlGameSpecSF07_return_1;
        }
    }
        /* (probably many) formulas are specified. check them all */
    else {
        CATCH(errmgr) {
                int i;
                int s = PropDb_get_size(prop_db);

                GameParams params;
                params.strategy_printout = strategy_printout;
                params.printout_as_dag = strategy_printout_as_dag;
                params.indented_printout = indented_printout;
                params.strategy_stream = strategy_stream;

                /* strategyFileName == NULL <-> strategy_stream == NULL */
                nusmv_assert(
                        (NIL(char) != strategyFileName ||
                (FILE*) NULL == strategy_stream) &&
                (NIL(char) == strategyFileName ||
                (FILE*) NULL != strategy_stream) );

                for (i=0; i < s; ++i) {
                    Prop_ptr p = PropDb_get_prop_at_index(prop_db, i);

                    if (Prop_get_type(p) == PropGame_LtlGame) {
                        Game_CheckLtlGameSpecSF07(env,PROP_GAME(p), &params, kmin, kmax, w);
                    }
                }
            }
        FAIL(errmgr) {
            goto CommandCheckLtlGameSpecSF07_return_1;
        }
    }
    goto CommandCheckLtlGameSpecSF07_return_0;

    CommandCheckLtlGameSpecSF07_return_usage:
    status = -1;
    goto CommandCheckLtlGameSpecSF07_cleanup_and_return;

    CommandCheckLtlGameSpecSF07_return_0:
    status = 0;
    goto CommandCheckLtlGameSpecSF07_cleanup_and_return;

    CommandCheckLtlGameSpecSF07_return_1:
    status = 1;
    goto CommandCheckLtlGameSpecSF07_cleanup_and_return;

    CommandCheckLtlGameSpecSF07_cleanup_and_return:
    if ((FILE*) NULL != strategy_stream) {
        CmdCloseFile(strategy_stream);
    }
    if (strategyFileName != NIL(char)) {
        FREE(strategyFileName);
    }
    if (useMore) {
        if (old_stdout != (FILE*) NULL) {
            CmdClosePipe(stdout);
            stdout = old_stdout;
        }
    }
    if (dbgFileName != NIL(char)) {
        if (old_stdout != (FILE*) NULL) {
            CmdCloseFile(stdout);
            stdout = old_stdout;
        }
        FREE(dbgFileName);
    }
    if (status == -1) {
        return UsageCheckLtlGameSpecSF07();
    } else {
        return status;
    }
}

static int UsageCheckLtlGameSpecSF07()
{
    fprintf(stderr,
            "usage: check_ltlgame_sf07 [-h] [-m | -o file] [-n number] [-s]\n");
    fprintf(stderr,
            "                          [-f strategy-file] [-d] [-e]\n");
    fprintf(stderr,
            "                          [-k number] [-K number] [-w p|a|b|1|2]\n");
    fprintf(stderr, "   -h \t\t\tPrints the command usage.\n");
    fprintf(stderr,
            "   -m \t\t\tPipes output through the program specified\n");
    fprintf(stderr,
            "      \t\t\tby the \"PAGER\" environment variable if defined,\n");
    fprintf(stderr, "      \t\t\telse through the UNIX command \"more\".\n");
    fprintf(stderr,
            "   -o file\t\tWrites the generated output to \"file\".\n");
    fprintf(stderr,
            "   -n number\t\tChecks LTLGAME specification with the given\n");
    fprintf(stderr, "      \t\t\tindex number.\n");
    fprintf(stderr,
            "   -s \t\t\tRequires strategy printout (default to stdout).\n");
    fprintf(stderr,
            "   -f file\t\tWrites strategy printout to \"file\" (implies -s).\n");
    fprintf(stderr,
            "   -d \t\t\tRequires strategy printout, generate a DAG printout.\n");
    fprintf(stderr, "      \t\t\t(implies -s)\n");
    fprintf(stderr,
            "   -e \t\t\tRequires strategy printout, generate an easy readable\n");
    fprintf(stderr, "      \t\t\tprintout. (implies -s)\n");
    fprintf(stderr, "   -k \t\t\tStart value for k (default 0).\n");
    fprintf(stderr, "   -K \t\t\tEnd value for k (default 20).\n");
    fprintf(stderr,
            "   -w \t\t\tWhom games are played for: (p)rotagonist, "
                    "(a)ntagonist,\n");
    fprintf(stderr,
            "      \t\t\t(b)oth, player (1), or player (2). Default: b.\n");

    return 1;
}

/**Function********************************************************************

  Synopsis           [ Extracts an (un)realizable core. ]

  CommandName        [ extract_unrealizable_core ]

  CommandSynopsis    [ Extracts an (un)realizable core. ]

  CommandArguments   [ \[-h\] \[-m | -o output-file\] \[-n number\]
                       \[-a algorithm\] \[-c type\]
                       \[-i\] \[-v\] \[-t\] \[-p\]
                       \[-w p|b|1|2\] \[-N number\] ]

  CommandDescription [ Extracts an (un)realizable core from a game +
                       property (after checking realizability of the
                       property, if needed). For details see
                       A. Cimatti, M. Roveri, V. Schuppan,
                       A. Tchaltsev: Diagnostic Information for
                       Realizability. In: VMCAI'08. <p>

                       The following two algorithms are available: <p>

                       actvars: an activation variable is introduced
                       for each part of the game that is to be
                       considered for minimization. Then the
                       parameterized realizability problem is solved
                       by a single call to the realizability
                       algorithm. The resulting set of (parameterized)
                       winning states is then used to extract the
                       core. <p>

                       explicit: the parts of the game that are to be
                       considered for minimization are removed
                       tentatively to see whether their removal
                       changes the outcome. If no, the removal is made
                       permanent; if yes, the removal is
                       undone. I.o.w., trial and error. <p>

                       Note that the two algorithms differ in what
                       they do when minimizing both players.

                       The following core types are available: <p>

                       core: This indicates which guarantees need to
                       be kept to preserve unrealizability
                       (resp. which assumptions need to be kept to
                       preserve realizability).

                       fix: This indicates which guarantees need to be
                       removed to obtain a realizable property
                       (resp. which assumptions need to be removed to
                       obtain unrealizability). Only available with
                       algorithm actvars.

  Command options:<p>
  <dl>
    <dt> <tt>-h</tt>
       <dd> Prints the command usage.
    <dt> <tt>-m</tt>
       <dd> Pipes the output generated by the command to the program
           specified by the <tt>PAGER</tt> shell variable if defined, else
           through the <tt>UNIX</tt> command "more".
    <dt> <tt>-o output-file</tt>
       <dd> Writes the output generated by the command to the file
           <tt>output-file</tt>.
    <dt> <tt>-n number</tt>
       <dd> Extracts the core of the property with the given index number.
    <dt> <tt>-a algorithm</tt>
       <dd> Uses algorithm <tt>algorithm</tt>. Available algorithms are
           <tt>actvars</tt> and <tt>explicit</tt> (default <tt>explicit</tt>).
    <dt> <tt>-c type</tt>
       <dd> Core type <tt>type</tt>. Available types are <tt>core</tt> and
           <tt>fix</tt> (only for algorithm actvars) (default <tt>core</tt>).
    <dt> <tt>-i</tt>
       <dd> Doesn't minimize INIT constraints.
    <dt> <tt>-v</tt>
       <dd> Doesn't minimize INVAR constraints.
    <dt> <tt>-t</tt>
       <dd> Doesn't minimize TRANS constraints.
    <dt> <tt>-p</tt>
       <dd> Doesn't minimize the property.
    <dt> <tt>-w w|b|1|2</tt>
       <dd> Who is minimized: <tt>l</tt>oser, <tt>b</tt>oth, player
           <tt>1</tt>, or player <tt>2</tt>. With algorithm actvars
           <tt>1</tt>, <tt>2</tt>, and <tt>b</tt> are available
           (default <tt>b</tt>. With algorithm explicit <tt>l</tt> and
           <tt>b</tt> are available (default <tt>l</tt>).
    <dt> <tt>-N number</tt>
       <dd> With algorithm actvars this specifies how many constraints are
           guarded by a single activation variable. 0 means no activation
           variables are introduced. Default: 1.
  </dl><p> ]

  SideEffects        [ ]

  SeeAlso            [ CommandCheck* ]

******************************************************************************/
static int CommandExtractUnrealizableCore(NuSMVEnv_ptr env,int argc, char **argv)
{
    int c;
    int useMore = 0;
    char* dbgFileName = NIL(char);
    FILE* old_stdout = (FILE*) NULL;
    int prop_no = -1;
    Game_UnrealizableCore_Algorithm algo =
            GAME_UNREALIZABLE_CORE_ALGORITHM_INVALID;
    Game_UnrealizableCore_CoreType ct =
            GAME_UNREALIZABLE_CORE_CORE_TYPE_INVALID;
    boolean min_init = true;
    boolean min_invar = true;
    boolean min_trans = true;
    boolean min_prop = true;
    Game_Who w = GAME_WHO_INVALID;
    int N = -1;
    int status;
    ErrorMgr_ptr const errmgr = ERROR_MGR(NuSMVEnv_get_value(env, ENV_ERROR_MANAGER));
    const NodeMgr_ptr nodemgr = NODE_MGR(NuSMVEnv_get_value(env, ENV_NODE_MGR));
    PropDb_ptr prop_db  = PROP_DB(NuSMVEnv_get_value(env, ENV_PROP_DB));

    nusmv_assert(opt_game_game(OptsHandler_create()));

    /*  Evaluate options. */

    util_getopt_reset();
    while ((c = util_getopt(argc, argv, "hmo:n:a:c:ivtpw:N:")) != EOF) {
        switch (c) {
            case 'h': goto CommandExtractUnrealizableCore_return_usage;
            case 'm':
                if (dbgFileName != NIL(char)) {
                    goto CommandExtractUnrealizableCore_return_usage;
                }
                useMore = 1;
                break;
            case 'o':
                if (useMore == 1) { goto CommandExtractUnrealizableCore_return_usage; }
                dbgFileName = util_strsav(util_optarg);
                fprintf(stdout, "Output to file: %s\n", dbgFileName);
                break;
            case 'n':
                if (prop_no != -1) { goto CommandExtractUnrealizableCore_return_usage; }
                prop_no = PropDb_get_prop_index_from_string(prop_db,
                                                            util_optarg);
                if (prop_no == -1) { goto CommandExtractUnrealizableCore_return_1; }
                break;
            case 'a':
            {
                char* strAlgo;
                if (algo != GAME_UNREALIZABLE_CORE_ALGORITHM_INVALID) {
                    goto CommandExtractUnrealizableCore_return_usage;
                }
                strAlgo = util_strsav(util_optarg);
                algo = Game_UnrealizableCore_Algorithm_from_string(strAlgo);
                if (algo == GAME_UNREALIZABLE_CORE_ALGORITHM_INVALID) {
                    goto CommandExtractUnrealizableCore_return_usage;
                }
                FREE(strAlgo);
            }
                break;
            case 'c':
            {
                char* strType;
                if (ct != GAME_UNREALIZABLE_CORE_CORE_TYPE_INVALID) {
                    goto CommandExtractUnrealizableCore_return_usage;
                }
                strType = util_strsav(util_optarg);
                ct = Game_UnrealizableCore_CoreType_from_string(strType);
                if (ct == GAME_UNREALIZABLE_CORE_CORE_TYPE_INVALID) {
                    goto CommandExtractUnrealizableCore_return_usage;
                }
                FREE(strType);
            }
                break;
            case 'i':
                if (!min_init) { goto CommandExtractUnrealizableCore_return_usage; }
                min_init = false;
                break;
            case 'v':
                if (!min_invar) { goto CommandExtractUnrealizableCore_return_usage; }
                min_invar = false;
                break;
            case 't':
                if (!min_trans) { goto CommandExtractUnrealizableCore_return_usage; }
                min_trans = false;
                break;
            case 'p':
                if (!min_prop) { goto CommandExtractUnrealizableCore_return_usage; }
                min_prop = false;
                break;
            case 'w':
            {
                char* strWho;
                if (w != GAME_WHO_INVALID) {
                    goto CommandExtractUnrealizableCore_return_usage;
                }
                strWho = util_strsav(util_optarg);
                w = Game_Who_from_string(strWho);
                if (w != GAME_WHO_LOSER &&
                    w != GAME_WHO_BOTH &&
                    w != GAME_WHO_PLAYER_1 &&
                    w != GAME_WHO_PLAYER_2) {
                    FREE(strWho);
                    goto CommandExtractUnrealizableCore_return_usage;
                }
                FREE(strWho);
            }
                break;
            case 'N':
            {
                char* strNumber;
                if (N != -1) { goto CommandExtractUnrealizableCore_return_usage; }
                strNumber = util_strsav(util_optarg);
                if (util_str2int(strNumber, &N) != 0) {
                    FREE(strNumber);
                    goto CommandExtractUnrealizableCore_return_usage;
                }
                if (N<0) {
                    FREE(strNumber);
                    goto CommandExtractUnrealizableCore_return_usage;
                }
                FREE(strNumber);
            }
                break;
            default: goto CommandExtractUnrealizableCore_return_usage;
        }
    }

    /*  Check option values. */

    if (argc != util_optind) { goto CommandExtractUnrealizableCore_return_usage; }

    if (algo == GAME_UNREALIZABLE_CORE_ALGORITHM_INVALID) {
        algo = DEFAULT_GAME_UNREALIZABLE_CORE_ALGORITHM;
    }

    if (ct == GAME_UNREALIZABLE_CORE_CORE_TYPE_INVALID) {
        ct = GAME_UNREALIZABLE_CORE_CORE_TYPE_CORE;
    }

    switch (algo) {
        case GAME_UNREALIZABLE_CORE_ALGORITHM_ACTIVATION_VARIABLES:
            if (w == GAME_WHO_INVALID) {
                w = GAME_WHO_BOTH;
            } else if (w != GAME_WHO_PLAYER_1 &&
                       w != GAME_WHO_PLAYER_2 &&
                       w != GAME_WHO_BOTH) {
                goto CommandExtractUnrealizableCore_return_usage;
            }
            if (N == -1) {
                N = DEFAULT_GAME_UNREALIZABLE_CORE_N;
            }
            break;
        case GAME_UNREALIZABLE_CORE_ALGORITHM_EXPLICIT:
            if (w == GAME_WHO_INVALID) {
                w = GAME_WHO_LOSER;
            } else if (w != GAME_WHO_LOSER &&
                       w != GAME_WHO_BOTH) {
                goto CommandExtractUnrealizableCore_return_usage;
            }
            if (ct != GAME_UNREALIZABLE_CORE_CORE_TYPE_CORE) {
                goto CommandExtractUnrealizableCore_return_usage;
            }
            if (N != -1) {
                goto CommandExtractUnrealizableCore_return_usage;
            }
            break;
        default:
            nusmv_assert(false);
    }

    /* Check preparations. */

    /* This command is only available in game mode. That means that a
       game model has been read. If this statement becomes false at some
       point, then insert a check for having read a model here. */

    if (Compile_check_if_encoding_was_built(env,stderr)) {
        goto CommandExtractUnrealizableCore_return_1;
    }

    if (Compile_check_if_model_was_built(env,stderr, false)) {
        goto CommandExtractUnrealizableCore_return_1;
    }

    if (useMore) {
        old_stdout = stdout;
        stdout = CmdOpenPipe(env,useMore);
        if (stdout==(FILE*) NULL) {
            stdout=old_stdout;
            old_stdout = (FILE*) NULL;
            goto CommandExtractUnrealizableCore_return_1;
        }
    }

    if (dbgFileName != NIL(char)) {
        old_stdout = stdout;
        stdout = CmdOpenFile(env,dbgFileName);
        if (stdout==(FILE*) NULL) {
            stdout = old_stdout;
            old_stdout = (FILE*) NULL;
            goto CommandExtractUnrealizableCore_return_1;
        }
    }

    /* Do the work. */

    /* One formula is specified. Process it. */
    if (prop_no != -1) {
        CATCH(errmgr) {
                Prop_ptr p = PropDb_get_prop_at_index(prop_db,
                                                      prop_no);

                PROP_CHECK_INSTANCE(p);
                if (Prop_get_type(p) != PropGame_GenReactivity) {
                    fprintf(stderr,
                            "Error: currently unrealizable core extraction is only "
                                    "available for GENREACTIVITY\n"
                                    "properties.\n");
                    goto CommandExtractUnrealizableCore_return_1;
                }
                Game_CheckGameSpecAndComputeCores(env,
                                                  nodemgr,
                                                  PROP_GAME(p),
                                                  algo,
                                                  ct,
                                                  min_init,
                                                  min_invar,
                                                  min_trans,
                                                  min_prop,
                                                  w,
                                                  N);
            }
        FAIL(errmgr) {
            goto CommandExtractUnrealizableCore_return_1;
        }
    }
        /* (probably many) formulas are specified. check them all */
    else {
        CATCH(errmgr) {
                int i;
                int s = PropDb_get_size(prop_db);

                for (i = 0; i < s; ++i) {
                    Prop_ptr p = PropDb_get_prop_at_index(prop_db, i);

                    PROP_CHECK_INSTANCE(p);
                    if (Prop_get_type(p) != PropGame_GenReactivity) {
                        fprintf(stderr,
                                "Warning: currently unrealizable core extraction is only "
                                        "available for GENREACTIVITY\n"
                                        "properties. Skipping property %d.\n", i);
                    } else {
                        Game_CheckGameSpecAndComputeCores(env,
                                                          nodemgr,
                                                          PROP_GAME(p),
                                                          algo,
                                                          ct,
                                                          min_init,
                                                          min_invar,
                                                          min_trans,
                                                          min_prop,
                                                          w,
                                                          N);
                    }
                }
            }
        FAIL(errmgr) {
            goto CommandExtractUnrealizableCore_return_1;
        }
    }
    goto CommandExtractUnrealizableCore_return_0;

    CommandExtractUnrealizableCore_return_usage:
    status = -1;
    goto CommandExtractUnrealizableCore_cleanup_and_return;

    CommandExtractUnrealizableCore_return_0:
    status = 0;
    goto CommandExtractUnrealizableCore_cleanup_and_return;

    CommandExtractUnrealizableCore_return_1:
    status = 1;
    goto CommandExtractUnrealizableCore_cleanup_and_return;

    CommandExtractUnrealizableCore_cleanup_and_return:
    if (useMore) {
        if (old_stdout != (FILE*) NULL) {
            CmdClosePipe(stdout);
            stdout = old_stdout;
        }
    }
    if (dbgFileName != NIL(char)) {
        if (old_stdout != (FILE*) NULL) {
            CmdCloseFile(stdout);
            stdout = old_stdout;
        }
        FREE(dbgFileName);
    }
    if (status == -1) {
        return UsageExtractUnrealizableCore();
    } else {
        return status;
    }
}

static int UsageExtractUnrealizableCore()
{
    fprintf(stderr,
            "usage: extract_unrealizable_core [-h] [-m | -o file] [-n number]\n");
    fprintf(stderr,
            "                                 [-a algorithm] [-c type]\n");
    fprintf(stderr,
            "                                 [-i] [-v] [-t] [-p]\n");
    fprintf(stderr,
            "                                 [-w l|b|1|2] [-N number]\n");
    fprintf(stderr,"   -h \t\t\tPrints the command usage.\n");
    fprintf(stderr,
            "   -m \t\t\tPipes output through the program specified\n");
    fprintf(stderr,
            "      \t\t\tby the \"PAGER\" environment variable if defined,\n");
    fprintf(stderr, "      \t\t\telse through the UNIX command \"more\".\n");
    fprintf(stderr,
            "   -o file\t\tWrites the generated output to \"file\".\n");
    fprintf(stderr,
            "   -n number\t\tExtracts the core of the property with the given\n");
    fprintf(stderr, "      \t\t\tindex number.\n");
    fprintf(stderr,
            "   -a algorithm\t\tUses algorithm \"algorithm\". Available "
                    "algorithms are\n");
    fprintf(stderr,
            "      \t\t\tactvars and explicit (default explicit).\n");
    fprintf(stderr,
            "   -c type\t\tProduces core type \"type\". Available types are core "
                    "and\n");
    fprintf(stderr,
            "      \t\t\tfix (only for algorithm actvars) (default core).\n");
    fprintf(stderr, "   -i \t\t\tDoesn't minimize INIT constraints.\n");
    fprintf(stderr, "   -v \t\t\tDoesn't minimize INVAR constraints.\n");
    fprintf(stderr, "   -t \t\t\tDoesn't minimize TRANS constraints.\n");
    fprintf(stderr, "   -p \t\t\tDoesn't minimize the property.\n");
    fprintf(stderr,
            "   -w l|b|1|2\t\tWho is minimized: (l)oser, (b)oth, player (1), "
                    "or\n");
    fprintf(stderr,
            "      \t\t\tplayer (2). With algorithm actvars \'1\', \'2\', and "
                    "\'b\'\n");
    fprintf(stderr,
            "      \t\t\tare available (default \'b\'). With algorithm explicit "
                    "\'l\'\n");
    fprintf(stderr,
            "      \t\t\tand \'b\' are available (default \'l\').\n");
    fprintf(stderr,
            "   -N number\t\tWith algorithm actvars this specifies how many\n");
    fprintf(stderr,
            "      \t\t\tconstraints are guarded by a single activation "
                    "variable.\n");
    fprintf(stderr,
            "      \t\t\t0 means no activation variales are introduced. "
                    "Default:\n");
    fprintf(stderr, "      \t\t\t1.\n");
    return 1;
}

/**Function********************************************************************

  Synopsis    [ Fills the commands in 'commands' into a NodeList. ]

  Description [ Helper function for Game_cmd_init. ]

  SideEffects [ ]

  SeeAlso     [ Game_cmd_init ]

******************************************************************************/
static NodeList_ptr game_cmd_init_commands_list(CommandDescr_t *commands,
                                                int len)
{
    NodeList_ptr res;
    int i;

    res = NodeList_create();
    for (i = 0; i < len; i++) {
        NodeList_append(res, NODE_PTR(&(commands[i])));
    }

    return res;
}
