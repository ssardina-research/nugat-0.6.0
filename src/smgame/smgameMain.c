/**CFile***********************************************************************

  FileName    [ smgameMain.c ]

  PackageName [ smgame ]

  Synopsis    [ Main NuGaT routine. Parses command line at invocation
                of NuGaT. ]

  Description [ ]

  SeeAlso     [ ]

  Author      [ Marco Roveri, Viktor Schuppan ]

  Copyright   [
  This file is part of the ``smgame'' package of NuGaT.
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

#if HAVE_CONFIG_H
# include "config.h"
#endif

#include "smgameInt.h"

#include "cmd/cmd.h"
#include "opt/opt.h"
#include "opt/optCmd.h"
#include "bmc/bmc.h"
#include "cinit/cinit.h" //#include "sm/sm.h"
#include "utils/utils.h"
#include "../addons/addons.h"
#include "smgameInt.h"
#include <stdio.h>
#include "../addons/game/gameInt.h"
#include <stdlib.h>
#include <sys/stat.h>
#include "printStrategy.h"

static char rcsid[] UTIL_UNUSED = "$Id: smMain.c,v 1.28.2.14.2.5.2.31.4.32 2010-02-23 13:38:37 nusmv Exp $";

/*---------------------------------------------------------------------------*/
/* Macro definitions                                                         */
/*---------------------------------------------------------------------------*/


/*---------------------------------------------------------------------------*/
/* Variable declarations                                                     */
/*---------------------------------------------------------------------------*/

/* Used to return a value from sm_parselineoptions */
static char * NuSMV_CMD_LINE = (char *) NULL;

EXTERN FILE* nusmv_stderr;
EXTERN FILE* nusmv_stdout;
EXTERN DDMgr_ptr dd_manager;

EXTERN GameParams gameParams;

/**AutomaticStart*************************************************************/

/*---------------------------------------------------------------------------*/
/* Static function prototypes                                                */
/*---------------------------------------------------------------------------*/

static void UsagePrint ARGS((const NuSMVEnv_ptr env,char * program, char * unknown_option));
static void BannerPrint ARGS((NuSMVEnv_ptr env,FILE * file));
static void sm_ParseLineOptions ARGS((const NuSMVEnv_ptr env,int argc, char ** argv,
                                      OptsHandler_ptr options));

/**AutomaticEnd***************************************************************/


/*---------------------------------------------------------------------------*/
/* Definition of exported functions                                          */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [ The main for NuGaT. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
int main(int  argc, char ** argv)
{
  int status = 0;
  NuSMVEnv_ptr env = NuSMVEnv_create();
  OptsHandler_ptr opts;

  boolean requires_shutdown = true;
  FP_V_E iq_fns[][2] = {{NuGaTAddons_Init, NuGaTAddons_Quit}};

  /* Initializes data such as tool name, tool version, email.. */
  NuSMVCore_init_data();

  /* Customize the library data. */
  NuSMVCore_set_tool_name("NuGAT-0.5.4");

  /* Initializes all packages, having the list of init/quit mfunctions */
  NuSMVCore_init(env,iq_fns, sizeof(iq_fns)/sizeof(iq_fns[0]));

  opts = OPTS_HANDLER(NuSMVEnv_get_value(env, ENV_OPTS_HANDLER));

  /* Adds the command line options of NuSMV */
  NuSMVCore_init_cmd_options(env);

  /* Add [or remove] custom command line options */
  //main_init_custom_cmd_options();


  Smgame_Init(env);

  int quit_flag;
  quit_flag = 0;

  sm_ParseLineOptions(env,argc, argv, opts);

  if (!opt_batch(opts)) { /* interactive mode */
    /* Initiliazes the commands to handle with options. */

    Opt_Cmd_init(env);
    BannerPrint(env,nusmv_stdout);
    if (!opt_ignore_init_file(opts)) {
      (void) Cmd_Misc_NusmvrcSource(env);
    }
    if (NuSMV_CMD_LINE != NULL) {
      /* Before entering interactive mode, check if command file
         actually exists and is readable. Failing to do so causes
         NuGaT to hang if source is not readable.
      */
      struct stat cmd_line;
      if (0 == stat(NuSMV_CMD_LINE, &cmd_line)) {
        char* command = ALLOC(char,
        strlen(NuSMV_CMD_LINE) + strlen("source ") + 1);
        sprintf(command, "source %s", NuSMV_CMD_LINE);
        quit_flag = Cmd_CommandExecute(env,command);
        FREE(command);
      }
      else {
        fprintf(nusmv_stderr, "No such file or directory. Exiting...\n");
        quit_flag = -1; /* require immediate quit */
      }
      FREE(NuSMV_CMD_LINE);
      NuSMV_CMD_LINE=(char*)NULL;
    }
    while (quit_flag >= 0) {
      quit_flag = Cmd_CommandExecute(env,"source -ip -");
    }
    status = 0;
  }
  else { /* batch mode */
    /* In the batch mode we dont want to read the ~/.nusmvrc file. */
    /* The system has to behave as the original NuGaT */
    /*   if (!opt_ignore_init_file(opts)) { */
    /*       (void) Sm_NusmvrcSource(); */
    /*     } */

    BannerPrint(env,nusmv_stdout);

    if (opt_verbose_level_gt(opts, 0)) {
      fprintf(nusmv_stdout, "Starting the batch interaction.\n");
    }

    Smgame_BatchMain(env);
  }

  /* Value of "quit_flag" is determined by the "quit" command */
  if (quit_flag == -1 || quit_flag == -2 || quit_flag == -4) {
    status = 0;
  }
  if (quit_flag == -2) {
    /*    Hrc_ManagerFree(globalHmgr); */
    Smgame_End(env);
  }
  else if (quit_flag == -3) {
    /* Script failed and on_failure_script_quits is set */
    /*    Hrc_ManagerFree(globalHmgr); */
    Smgame_End(env);
    status = -1;
  }
  else if (quit_flag == -4) {
    /* exits quickly and silently */
  }
  else {
    Smgame_End(env);
  }

  exit(status);
}


/*---------------------------------------------------------------------------*/
/* Definition of internal functions                                          */
/*---------------------------------------------------------------------------*/


/*---------------------------------------------------------------------------*/
/* Definition of static functions                                            */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [ Prints the usage of the NuGaT shell interface. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
static void UsagePrint(const NuSMVEnv_ptr env,char * program, char * unknown_option)
{
  char *libraryName;

  BannerPrint(env,nusmv_stderr);

  fprintf(nusmv_stderr,"\n");

  if (unknown_option != NULL) {
    fprintf(nusmv_stderr,
            "The command line option \"%s\" is unknown.\n",
            unknown_option);
  }
  fprintf(nusmv_stderr,
          "Usage:\t%s [-h | -help]  [-quiet] [-int] \\\n",
          program);
  fprintf(nusmv_stderr,
      "\t[[-source script_file | -load script_file]] \\\n"
      "\t[-s] [-old] [-old_div_op] [-dcx] \\\n"
      "\t[-ctt] [-lp] [-n idx] [-v vl] [-cpp] [-pre pp_list] \\\n"
      "\t[-is] [-ic] [-ils] [-ips] [-ii] [[-r] [-f]]|[-df] [-flt] [-AG] \\\n"
      "\t[-i iv_file] [-o ov_file] [-t tv_file] [-reorder] [-dynamic] \\\n"
      "\t[-m method] [-disable_bdd_cache] [-bdd_soh heuristics]\\\n"
      "\t[[-mono]|[-thresh cp_t]|[-cp cp_t]|[-iwls95 cp_t]] \\\n"
      "\t[-coi] [-noaffinity] [-iwls95preorder] [-bmc] [-sat_solver name] \\\n"
      "\t[-bmc_length k] [-ofm fm_file] [-obm bm_file] \\\n"
      "\t[-sin on|off] [-rin on|off] [-ojeba algorithm] \\\n");
  fprintf(nusmv_stderr, "\t[input-file]\n");

  fprintf(nusmv_stderr, "Where:\n");
  fprintf(nusmv_stderr, "\t -h | -help\t prints out current message\n");
  fprintf(nusmv_stderr, "\t -quiet\t\t suppresses printing of the banner\n");
  fprintf(nusmv_stderr, "\t -int\t\t enables interactive mode\n");
  fprintf(nusmv_stderr, "\t -source sc_file executes %s commands from file \"sc_file\"\n", program);
  fprintf(nusmv_stderr, "\t -load sc_file\t same as -source (deprecated)\n");
  fprintf(nusmv_stderr, "\t              \t in the interactive shell.\n");
  {
    fprintf(nusmv_stderr, "\t -s\t\t does not read any initialization file\n");
    libraryName = CInit_NuSMVObtainLibrary();
    fprintf(nusmv_stderr, "\t   \t\t (%s/master.nusmvrc, ~/.nusmvrc)\n\t\t\t (default in batch mode)\n", libraryName);
    FREE(libraryName);
  }
  fprintf(nusmv_stderr, "\t -old\t\t keeps backward compatibility with older versions of \n"
                        "\t\t\t %s\n", program);
  fprintf(nusmv_stderr, "\t -old_div_op \t enables the old semantics of \"/\" and \"mod\" operations\n"
                        "\t\t\t instead of ANSI C semantics\n");
  fprintf(nusmv_stderr, "\t -dcx \t\t disables computation of counter-examples \n");
  fprintf(nusmv_stderr, "\t -ctt\t\t enables checking for the totality of the transition\n\t\t\t relation\n");
  fprintf(nusmv_stderr, "\t -lp\t\t lists all properties in SMV model\n");
  fprintf(nusmv_stderr, "\t -n idx\t\t specifies which property of SMV model\n" \
          "\t\t\t should be checked\n");
  fprintf(nusmv_stderr, "\t -v vl\t\t sets verbose level to \"vl\"\n");
  {
    fprintf(nusmv_stderr, "\t -cpp\t\t runs preprocessor on SMV files before\n"
            "\t\t\t any specified with -pre.\n");
# if HAVE_CPP
#   if HAVE_GETENV
    fprintf(nusmv_stderr, "\t\t\t Environment variable 'CPP' can be used to\n");
    fprintf(nusmv_stderr, "\t\t\t specify a different preprocessor.\n");
#   endif
# else
    fprintf(nusmv_stderr, "\t\t\t Preprocessor was not found when %s had been \n", program);
    fprintf(nusmv_stderr, "\t\t\t configured, then 'cpp' will be searched at runtime\n");
    fprintf(nusmv_stderr, "\t\t\t when needed");
#   if HAVE_GETENV
    fprintf(nusmv_stderr, ", or the 'CPP' environment variable\n");
    fprintf(nusmv_stderr, "\t\t\t will be used when defined by the user");
#   endif
    fprintf(nusmv_stderr, ".\n");
# endif
    fprintf(nusmv_stderr, "\t\t\t Deprecated: use -pre option instead.\n");
  }
  {
    fprintf(nusmv_stderr, "\t -pre pp_list\t defines a space-separated list of pre-processors\n"\
            "\t\t\t to run (in the order given) on the input file.\n"\
            "\t\t\t The list must be in double quotes if there is more\n"\
            "\t\t\t than one pre-processor named.\n");
    if (get_preprocessors_num(env) > 0) {
      char* preps = get_preprocessor_names(env);
      fprintf(nusmv_stderr, "\t\t\t The available preprocessors are: %s\n", preps);
      FREE(preps);
    }
    else {
      fprintf(nusmv_stderr, "\t\t\t Warning: there are no available preprocessors.\n");
    }
  }
  fprintf(nusmv_stderr, "\t -is\t\t does not check SPEC\n");
  fprintf(nusmv_stderr, "\t -ic\t\t does not check COMPUTE\n");
  fprintf(nusmv_stderr, "\t -ils\t\t does not check LTLSPEC\n");
  fprintf(nusmv_stderr, "\t -ips\t\t does not check PSLSPEC\n");
  fprintf(nusmv_stderr, "\t -ii\t\t does not check INVARSPEC\n");
  fprintf(nusmv_stderr, "\t -r\t\t enables printing of reachable states\n");
  fprintf(nusmv_stderr, "\t -f\t\t computes the reachable states (forward search)\n"
                        "\t\t\t (default)\n");
  fprintf(nusmv_stderr, "\t -df\t\t disables the computation of reachable states\n");
  fprintf(nusmv_stderr, "\t -flt\t\t computes the reachable states also for the LTL Tableau\n");
  fprintf(nusmv_stderr, "\t -AG\t\t enables AG only search\n");
  fprintf(nusmv_stderr, "\t -i iv_file\t reads order of variables from file \"iv_file\"\n");
  fprintf(nusmv_stderr, "\t -o ov_file\t prints order of variables to file \"ov_file\"\n");
  fprintf(nusmv_stderr, "\t -t tv_file\t reads order of vars for clustering from file \"tv_file\"\n");
  fprintf(nusmv_stderr, "\t -reorder\t enables reordering of variables before exiting\n");
  fprintf(nusmv_stderr, "\t -dynamic\t enables dynamic reordering of variables\n");
  fprintf(nusmv_stderr, "\t -m method\t sets the variable ordering method to \"method\".\n");
  fprintf(nusmv_stderr, "\t\t\t Reordering will be activated\n");
  fprintf(nusmv_stderr, "\t -disable_bdd_cache    disables caching of expressions evaluation to BDD\n");
  fprintf(nusmv_stderr, "\t -bdd_soh heuristics   sets the static variable ordering heuristics\n"
                        "\t\t\t to \"heuristics\".\n");
  fprintf(nusmv_stderr, "\t -mono\t\t enables monolithic transition relation\n");
  fprintf(nusmv_stderr, "\t -thresh cp_t\t conjunctive partitioning with threshold of each\n");
  fprintf(nusmv_stderr, "\t\t\t partition set to \"cp_t\" (DEFAULT, with cp_t=1000)\n");
  fprintf(nusmv_stderr, "\t -cp cp_t\t DEPRECATED: use -thresh instead.\n");
  fprintf(nusmv_stderr, "\t -iwls95 cp_t\t enables Iwls95 conjunctive partitioning and sets\n");
  fprintf(nusmv_stderr, "\t\t\t the threshold of each partition to \"cp_t\"\n");
  fprintf(nusmv_stderr, "\t -coi\t\t enables cone of influence reduction\n");
  fprintf(nusmv_stderr, "\t -noaffinity\t disables affinity clustering\n");
  fprintf(nusmv_stderr, "\t -iwls95preorder enables iwls95 preordering\n");
  fprintf(nusmv_stderr, "\t -bmc\t\t enables BMC instead of BDD model checking\n");
  fprintf(nusmv_stderr, "\t -sat_solver str sets the sat_solver variable, used by BMC\n");
  fprintf(nusmv_stderr,"\t\t\t "); Sat_PrintAvailableSolvers(nusmv_stderr);
  fprintf(nusmv_stderr, "\t -bmc_length k\t sets bmc_length variable, used by BMC\n");
  fprintf(nusmv_stderr, "\t -ofm fm_file\t prints flattened model to file \"fn_file\"\n");
  fprintf(nusmv_stderr, "\t -obm bm_file\t prints boolean model to file \"bn_file\"\n");
  fprintf(nusmv_stderr, "\t -sin on|off\t enables (on) or disables sexp inlining (default is off)\n");
  fprintf(nusmv_stderr, "\t -rin on|off\t enables (on) or disables rbc inlining (default is on)\n");
  {
    fprintf(nusmv_stderr, "\t -ojeba str \t sets the algorthim used for BDD-based language\n"
            "\t\t\t emptiness of B�chi fair transition systems\n"
            "\t\t\t (default is %s)\n",
            Bdd_BddOregJusticeEmptinessBddAlgorithmType_to_string(DEFAULT_OREG_JUSTICE_EMPTINESS_BDD_ALGORITHM));
    fprintf(nusmv_stderr,"\t\t\t ");
    Bdd_print_available_BddOregJusticeEmptinessBddAlgorithms(nusmv_stderr);
  }
  fprintf(nusmv_stderr, "\t input-file\t the file both the model and \n");
  fprintf(nusmv_stderr, "\t\t\t the spec were read from\n");

  exit(2);
}

/**Function********************************************************************

  Synopsis    [ Prints the banner of NuGaT. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
static void BannerPrint(NuSMVEnv_ptr env,FILE * file)
{

  OptsHandler_ptr opts = OPTS_HANDLER(NuSMVEnv_get_value(env, ENV_OPTS_HANDLER));

  /* Do not print the NuGaT banner if in quiet mode.. */
  if (opt_get_quiet_mode(opts)) return;

  fprintf(file, "*** This is %s\n", Smgame_NuGaTReadVersion());
# ifdef LINKED_ADDONS
  /* linked addons are printed only if not empty */
  if (strcmp(LINKED_ADDONS, "") != 0) {
    fprintf(file, "*** Enabled addons are: %s\n", LINKED_ADDONS);
  }
#endif
  fprintf(file,
          "*** For more information on NuGaT see <http://es.fbk.eu/tools/nugat>\n");
  fprintf(file, "*** or email to <nugat-users@list.fbk.eu>.\n");
  fprintf(file, "*** Please report bugs to <%s>.\n", PACKAGE_BUGREPORT);
  fprintf(file, "*** Copyright (c) 2010, Fondazione Bruno Kessler\n\n");

  CInit_BannerPrint_nusmv_library(file);

  /* Cudd license */
  CInit_BannerPrint_cudd(file);

# if HAVE_SOLVER_MINISAT
    CInit_BannerPrint_minisat(file);
# endif

# if HAVE_SOLVER_ZCHAFF
    CInit_BannerPrint_zchaff(file);
# endif

#if HAVE_GAME
#else
  fprintf(file, "*************************************************************************\n");
  fprintf(file, "*************************************************************************\n");
  fprintf(file, "*** WARNING: game addon not configured.                               ***\n");
  fprintf(file, "*** WARNING: Game functionality not available.                        ***\n");
  fprintf(file, "*** WARNING: Consider configuring with --enable-addons=game.          ***\n");
  fprintf(file, "*************************************************************************\n");
  fprintf(file, "*************************************************************************\n");
#endif

  fflush(NULL); /* to flush all the banner before any other output */
}

/**Function********************************************************************

  Synopsis    [ Parses the command line options. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
static void sm_ParseLineOptions(const NuSMVEnv_ptr env,int argc, char ** argv, OptsHandler_ptr options)
{
  /* parses the Program Name */
  argc--;
  set_pgm_path(options, *(argv++));

  while (argc > 0) {
    if (strcmp(*argv, "-h") == 0) {
      argv++; argc--;
      UsagePrint(env,get_pgm_path(options), NULL);
    }
    else if (strcmp(*argv, "-help") == 0) {
      argv++; argc--;
      UsagePrint(env,get_pgm_path(options), NULL);
    }
    else if (strcmp(*argv,"-quiet") == 0) {
      argv++; argc--;
      set_quiet_mode(options);
      continue;
    }
    else if (strcmp(*argv,"-int") == 0){
      argv++; argc--;
      unset_batch(options);

#if HAVE_SETVBUF
# if SETVBUF_REVERSED
      setvbuf(nusmv_stdout, _IOLBF, (char *) NULL, 0);
# else
      setvbuf(nusmv_stdout, (char *) NULL, _IOLBF, 0);
# endif
#endif

      continue;
    }
    else if ((0 == strcmp(*argv, "-source")) || (strcmp(*argv,"-load") == 0)) {
      argc--;
      if (argc == 0) {
        fprintf(nusmv_stderr,
                "The \"%s\" command line options requires an argument.\n",
                (*argv));
        exit(1);
      }
      if (0 == strcmp(*argv, "-load")) {
        fprintf(nusmv_stderr,
                "WARNING: -load is deprecated, use -source instead.\n");
      }
      argv++;

      unset_batch(options); /* goes in interactive mode by default */
      NuSMV_CMD_LINE = ALLOC(char, strlen(*argv)+1);
      strcpy(NuSMV_CMD_LINE, *argv);
      fprintf(nusmv_stderr, "FILE ->>> %s \n", NuSMV_CMD_LINE);
      argv++; argc--;
      continue;
    }
    else if(strcmp(*argv,"-s") == 0){
      argv++;
      argc--;
      set_ignore_init_file(options);
      continue;
    }
    else if (strcmp(*argv, "-old") == 0) {
      argv++; argc--;
      set_backward_comp(options);
      continue;
    }
    else if (strcmp(*argv, "-old_div_op") == 0) {
      argv++; argc--;
      unset_use_ansi_c_div_op(options);
      continue;
    }
    else if (strcmp(*argv, "-dcx") == 0) {
      argv++; argc--;
      unset_counter_examples(options);
      continue;
    }
    else if (strcmp(*argv, "-ctt") == 0) {
      argv++; argc--;
      set_check_fsm(options);
      continue;
    }
    else if (strcmp(*argv,"-lp") == 0){
      argv++; argc--;
      set_list_properties(options);
      continue;
    }
    else if (strcmp(*argv,"-n") == 0){
      if (argc < 2) {
        fprintf(nusmv_stderr, "The \"-n\" command line option requires an argument.\n");
        exit(1);
      }
      {
        char *err_occ[1];
        int prop_no;

        err_occ[0] = "";
        argv++; argc -= 2;
        prop_no = strtol(*(argv++),err_occ, 10);
        if (strcmp(err_occ[0], "") != 0) {
          fprintf(nusmv_stderr, "Error: \"%s\" is not a valid value for the \"-n\" command line option.\n", err_occ[0]);
          exit(1);
        }
        if (prop_no < 0) {
          fprintf(nusmv_stderr, "Error: \"%d\" is not a valid value for the \"-n\" command line option.\n", prop_no);
          exit(1);
        }
        set_prop_no(options, prop_no);
      }
      continue;
    }
    else if (strcmp(*argv,"-v") == 0){
      if (argc < 2) {
        fprintf(nusmv_stderr, "The \"-v\" command line option requires an argument.\n");
        exit(1);
      }
      {
        char *err_occ[1];
        int cur_verbose;

        err_occ[0] = "";
        argv++; argc -= 2;
        cur_verbose = strtol(*(argv++),err_occ, 10);
        if (strcmp(err_occ[0], "") != 0) {
          fprintf(nusmv_stderr, "Error: \"%s\" is not a valid value for the \"-v\" command line option.\n", err_occ[0]);
          exit(1);
        }
        set_verbose_level(options, cur_verbose);
      }
#if HAVE_SETVBUF
# if SETVBUF_REVERSED
      setvbuf(nusmv_stdout, _IOLBF, (char *) NULL, 0);
# else
      setvbuf(nusmv_stdout, (char *)NULL, _IOLBF, 0);
# endif
#endif
      continue;
    }
#   if HAVE_CPP
    else if (strcmp(*argv,"-cpp") == 0) {
      /* If -cpp option is specified then cpp is
         made the first preprocessor to use */
      char* pp_list;
      argv++; argc--;
      pp_list = get_pp_list(options);
      if (strcmp(pp_list, "") == 0) {
        set_pp_list(options, "cpp", env);
      }
      else {
        char* new_pp_list;
        new_pp_list = ALLOC(char, strlen(pp_list) + 5);
        strcpy(new_pp_list, "cpp ");
        strcat(new_pp_list, pp_list);
        set_pp_list(options, new_pp_list, env);
        FREE(new_pp_list);
      }
      continue;
    }
#   endif
    else if (strcmp(*argv, "-pre") == 0) {
      char * preprocessors;
      char * pp_list;
      if (argc-- < 2) {
        fprintf(nusmv_stderr, "The \"-pre\" command line option requires an argument.\n");
        exit(1);
      }
        argv++; argc--;
        preprocessors = *(argv++);
        pp_list = get_pp_list(options);
        if (strcmp(pp_list, "") == 0) {
          set_pp_list(options, preprocessors, env);
        }
        else {
          char* new_pp_list;

          new_pp_list = ALLOC(char, strlen(pp_list) + strlen(preprocessors) + 2);
          strcpy(new_pp_list, pp_list);
          strcat(new_pp_list, " ");
          strcat(new_pp_list, preprocessors);
          set_pp_list(options, new_pp_list, env);
          FREE(new_pp_list);
        }

      continue;
    }
    if (strcmp(*argv,"-is") == 0){
      argv++; argc--;
      set_ignore_spec(options);
      continue;
    }
    if (strcmp(*argv,"-ic") == 0){
      argv++; argc--;
      set_ignore_compute(options);
      continue;
    }
    if (strcmp(*argv,"-ils") == 0){
      argv++; argc--;
      set_ignore_ltlspec(options);
      continue;
    }
    if (strcmp(*argv,"-ips") == 0){
      argv++; argc--;
      set_ignore_pslspec(options);
      continue;
    }
    else if (strcmp(*argv,"-ii") == 0){
      argv++; argc--;
      set_ignore_invar(options);
      continue;
    }
    else if (strcmp(*argv,"-r") == 0){
      argv++; argc--;
      set_print_reachable(options);
      set_forward_search(options);
      /* if this option is used, also their use is enabled */
      set_use_reachable_states(options);
      continue;
    }
    else if (strcmp(*argv,"-f") == 0){
      argv++; argc--;
      set_forward_search(options);
      /* if this option is used, also their use is enabled */
      set_use_reachable_states(options);
      continue;
    }
    else if (strcmp(*argv,"-df") == 0){
      argv++; argc--;
      unset_forward_search(options);
      /* if this option is used, also their use is enabled */
      unset_use_reachable_states(options);
      continue;
    }
    else if (strcmp(*argv,"-flt") == 0){
      argv++; argc--;
      set_ltl_tableau_forward_search(options);
      continue;
    }
    else if (strcmp(*argv,"-AG") == 0){
      argv++; argc--;
      set_ag_only(options);
      continue;
    }
    else if (strcmp(*argv, "-i") == 0){
      argv++; argc -= 2;
      set_input_order_file(options, *(argv++));
      continue;
    }
    else if (strcmp(*argv, "-o") == 0){
      argv++;  argc -= 2;
      set_output_order_file(options, *(argv++));
      continue;
    }
    else if (strcmp(*argv, "-t") == 0){
      argv++;  argc -= 2;
      set_trans_order_file(options, *(argv++));
      continue;
    }
    else if (strcmp(*argv, "-reorder") == 0) {
      argv++; argc--;
      set_reorder(options);
      continue;
    }
    else if (strcmp(*argv, "-dynamic") == 0) {
      argv++; argc--;
      set_dynamic_reorder(options);
      dd_autodyn_enable(dd_manager, dd_get_ordering_method(dd_manager));
      continue;
    }
    else if (strcmp(*argv, "-m") == 0){
      if (argc < 2) {
        fprintf(nusmv_stderr, "The \"-m\" command line option requires an argument.\n");
        exit(1);
      }
      argv++; argc -= 2;
      {
        unsigned int reorder_method = StringConvertToDynOrderType(*argv);
        if ( reorder_method == REORDER_NONE) {
          fprintf(nusmv_stderr, "The method \"%s\" is not a valid reorder method.\n",
                         *argv);
          exit(1);
        }
        argv++;
        set_reorder_method(options, reorder_method);
      }
      continue;
    }
    else if (strcmp(*argv, "-disable_bdd_cache") == 0) {
      argv++; argc--;
      unset_enable_sexp2bdd_caching(options);
      continue;
    }
    else if (strcmp(*argv, "-bdd_soh") == 0){
      if (argc < 2) {
        fprintf(nusmv_stderr, "The \"-bdd_soh\" command line option requires an argument.\n");
        exit(1);
      }
      argv++; argc -= 2;
      {
        BddSohEnum value = Enc_string_to_bdd_static_order_heuristics(*argv);
        if (value == BDD_STATIC_ORDER_HEURISTICS_ERROR) {
          fprintf(nusmv_stderr, "The heuristics \"%s\" is not a valid static vars ordering heuristics.\n"
                  "Valid values are: %s\n",
                  *argv, Enc_get_valid_bdd_static_order_heuristics());
          exit(1);
        }
        argv++;
        set_bdd_static_order_heuristics(options, value);
      }
      continue;
    }
    else if(strcmp(*argv,"-mono") == 0){
      argv++;
      argc--;
      set_monolithic(options);
      continue;
    }
    else if((strcmp(*argv, "-cp") == 0) || (strcmp(*argv, "-thresh") == 0)){
      if (argc < 2) {
        fprintf(nusmv_stderr, "The \"-thresh\" (or \"-cp\") command line option requires an argument.\n");
        exit(1);
      }
      {
        char *err_occ[1];
        int cur_cpl;

        err_occ[0] = "";
        argv++; argc -= 2;
        cur_cpl = strtol(*(argv++), err_occ, 10);
        if (strcmp(err_occ[0], "") != 0) {
          fprintf(nusmv_stderr, "Error: \"%s\" is not a valid value for the \"-cp\" line option.\n", err_occ[0]);
          exit(1);
        }
        set_conj_partitioning(options);
        set_conj_part_threshold(options, cur_cpl);
      }
      continue;
    }
    else if(strcmp(*argv, "-iwls95") == 0){
      if (argc < 2) {
        fprintf(nusmv_stderr, "The \"-iwls95\" command line option requires an argument.\n");
        exit(1);
      }
      {
        char *err_occ[1];
        int cur_cpl;

        err_occ[0] = "";
        argv++; argc -= 2;
        cur_cpl = strtol(*(argv++), err_occ, 10);
        if (strcmp(err_occ[0], "") != 0) {
          fprintf(nusmv_stderr, "Error: \"%s\" is not a valid value for the \"-iwls95\" line option.\n", err_occ[0]);
          exit(1);
        }
        set_iwls95cp_partitioning(options);
        set_image_cluster_size(options, cur_cpl);
      }
      continue;
    }
    else if (strcmp(*argv, "-coi") == 0) {
      argv++; argc--;
      set_cone_of_influence(options);
      continue;
    }
    else if (strcmp(*argv,"-noaffinity") == 0){
      argv++; argc--;
      unset_affinity(options);
      continue;
    }
    else if (strcmp(*argv,"-iwls95preorder") == 0){
      argv++; argc--;
      set_iwls95_preorder(options);
      continue;
    }
#if HAVE_SAT_SOLVER
    else if (strcmp(*argv,"-bmc") == 0){
      argv++; argc--;
      set_bmc_mode(options);
      continue;
    }
    else if (strcmp(*argv,"-sat_solver") == 0) {
      if (argc < 2) {
        fprintf(nusmv_stderr, "The \"-sat_solver\" command line option requires an argument.\n");
        exit(1);
      }
      argv++; argc--;
      {
        const char* satSolver = *(argv);
        const char* normalizedSatSolver = Sat_NormalizeSatSolverName(satSolver);
        argv++; argc--;
        if (normalizedSatSolver == (const char*) NULL) {
          fprintf(nusmv_stderr,
                  "Error: \"%s\" is not a valid value for the \"-sat_solver\" command line option.\n",
                  satSolver);
          Sat_PrintAvailableSolvers(nusmv_stderr);
          exit(1);
        }

        set_sat_solver(options, normalizedSatSolver);
      }
      continue;
    }
    else if (strcmp(*argv,"-bmc_length") == 0){
      if (argc < 2) {
        fprintf(nusmv_stderr, "The \"-bmc_length\" command line option requires an argument.\n");
        exit(1);
      }
      {
        char *err_occ[1];
        int bmc_length;

        err_occ[0] = "";
        argv++; argc -= 2;
        bmc_length = strtol(*(argv++),err_occ, 10);
        if (strcmp(err_occ[0], "") != 0) {
          fprintf(nusmv_stderr, "Error: \"%s\" is not a valid value for the \"-bmc_length\" command line option.\n", err_occ[0]);
          exit(1);
        }
        if (bmc_length < 0) {
          fprintf(nusmv_stderr, "Error: \"%d\" is not a valid value for the \"-bmc_length\" command line option.\n", bmc_length);
          exit(1);
        }
        set_bmc_pb_length(options, bmc_length);
      }
      continue;
    }
#endif /* No sat solver available */
    else if (strcmp(*argv, "-ofm") == 0){
      argv++;  argc -= 2;
      set_output_flatten_model_file(options, *(argv++));
      continue;
    }
    else if (strcmp(*argv, "-obm") == 0){
      argv++;  argc -= 2;
      set_output_boolean_model_file(options, *(argv++));
      continue;
    }
    else if (strcmp(*argv, "-sin") == 0) {
      char* val;
      if (argc < 2) {
        fprintf(nusmv_stderr, "The \"-sin\" command line option requires an argument.\n");
        exit(1);
      }
      argv++; argc -= 2;
      val = *(argv++);
      if (strcmp(val , "off") == 0) unset_symb_inlining(options);
      else if (strcmp(val, "on") == 0) set_symb_inlining(options);
      else {
        fprintf(nusmv_stderr, "Error: \"%s\" is not a valid value for the \"-sin\" command line option.\n", val);
        exit(1);
      }
      continue;
    }
    else if (strcmp(*argv, "-rin") == 0) {
      char* val;
      if (argc < 2) {
        fprintf(nusmv_stderr, "The \"-rin\" command line option requires an argument.\n");
        exit(1);
      }
      argv++; argc -= 2;
      val = *(argv++);
      if (strcmp(val, "off") == 0) unset_rbc_inlining(options);
      else if (strcmp(val, "on") == 0) set_rbc_inlining(options);
      else {
        fprintf(nusmv_stderr, "Error: \"%s\" is not a valid value for the \"-rin\" command line option.\n", val);
        exit(1);
      }
      continue;
    }
    else if (strcmp(*argv, "-ojeba") == 0){
      if (argc < 2) {
        fprintf(nusmv_stderr,
                "The \"-ojeba\" command line option requires an argument.\n");
        exit(1);
      }
      argv++; argc -= 2;
      {
        BddOregJusticeEmptinessBddAlgorithmType alg =
          Bdd_BddOregJusticeEmptinessBddAlgorithmType_from_string(*argv);
        if (alg == BDD_OREG_JUSTICE_EMPTINESS_BDD_ALGORITHM_INVALID) {
          fprintf(nusmv_stderr,
                  "The algorithm \"%s\" is not a valid BDD-based "\
                  "algorithm to check language emptiness for omega-"\
                  "regular properties.\n",
                  *argv);
          Bdd_print_available_BddOregJusticeEmptinessBddAlgorithms(nusmv_stderr);
          exit(1);
        }
        argv++;
        set_oreg_justice_emptiness_bdd_algorithm(options, alg);
      }
      continue;
    }
    else if(strcmp(*argv, "-dp") == 0){
      argv++; argc--;
      fprintf(nusmv_stderr, "WARNING: Disjunctive partitioning is no longer supported.\n");
      continue;
    }
      /* printing strategy options */
    else if(strcmp(*argv, "-e") == 0){
      argv++; argc--;
      /* -e implies -s */
      gameParams.strategy_printout = 1;
      gameParams.indented_printout = 1;
      continue;
    }
    else if(strcmp(*argv, "-s") == 0){
      argv++; argc--;
      gameParams.strategy_printout = 1;
      continue;
    }
    else if (argc == 1 && (**argv) != '-'){
      set_input_file(options, *(argv++));
      argc--;
      continue;
    }
    else  {
      UsagePrint(env,get_pgm_path(options), *argv);
    }
  }
}
