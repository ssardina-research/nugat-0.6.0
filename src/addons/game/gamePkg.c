/**CFile***********************************************************************

  FileName    [ gamePkg.c ]

  PackageName [ game ]

  Synopsis    [ Package init/quit and mode entry/exit functions. ]

  Description [ ]

  SeeAlso     [ game.h ]

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

#include "gameInt.h"
#include "gameCmd.h"
#include "GameHierarchy.h"
#include "PropDbGame.h"
#include "walkers/CheckerGame.h"
#include "walkers/PrinterGame.h"
#include "walkers/PrinterSexpGame.h"

#include "cmd/cmd.h"
#include "cmd/cmdInt.h"
#include "compile/compile.h"
#include "node/node.h"
#include "node/MasterNodeWalker.h"
#include "node/NodeWalker.h"
#include "node/printers/MasterPrinter.h"
#include "opt/opt.h"
#include "prop/propPkg.h"
#include "set/set.h"
#include "utils/utils.h"
#include "utils/avl.h"
#include "utils/error.h"
#include "utils/ustring.h"
#include "utils/NodeList.h"

#include <stdio.h>

/*---------------------------------------------------------------------------*/
static char rcsid[] UTIL_UNUSED = "$Id: gameGeneral.c,v 1.1.2.9 2010-02-05 17:19:08 nusmv Exp $";
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Structure declarations                                                    */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Type declarations                                                         */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Variable declarations                                                     */
/*---------------------------------------------------------------------------*/

/**Variable********************************************************************

  Synopsis    [ These two variables store the commands that are disabled
                upon entering game mode for latter reenabling when leaving
                game mode. ]

  Description [ Not specific to game. ]

  SeeAlso     [ ]

******************************************************************************/
static NodeList_ptr stored_dependent = NODE_LIST(NULL);
static NodeList_ptr stored_specific = NODE_LIST(NULL);

EXTERN FILE* nusmv_stderr;
EXTERN FILE* nusmv_stdout;

/*---------------------------------------------------------------------------*/
/* Macro declarations                                                        */
/*---------------------------------------------------------------------------*/

/**AutomaticStart*************************************************************/

/*---------------------------------------------------------------------------*/
/* Static function prototypes                                                */
/*---------------------------------------------------------------------------*/
static void game_pkg_switch_to_prop_db_game ARGS((void));
static void game_pkg_switch_to_prop_db ARGS((void));
static void game_pkg_switch_to_game_cmds ARGS((NodeList_ptr generic,
                                               NodeList_ptr dependent,
                                               NodeList_ptr specific));
static void game_pkg_switch_from_game_cmds ARGS((NodeList_ptr dependent,
                                                 NodeList_ptr specific));
static void game_pkg_add_cmds ARGS((NodeList_ptr commands));
static void game_pkg_remove_cmds ARGS((NodeList_ptr commands));
static void game_pkg_store_remove_cmd ARGS((char* name, NodeList_ptr stored));
static void game_pkg_restore_cmds ARGS((NodeList_ptr* stored));

/*---------------------------------------------------------------------------*/
/* Definition of exported functions                                          */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [ Initializes the game package. ]

  Description [ This is called when starting and resetting NuGaT. ]

  SideEffects [ ]

  SeeAlso     [ Game_Quit, Game_Mode_Enter ]

******************************************************************************/
void Game_Init(void)
{
  if (opt_verbose_level_gt(OptsHandler_create(), 0)) {
    fprintf(nusmv_stderr, "Initializing the Game package... \n");
  }

  nusmv_assert(GAME_HIERARCHY(NULL) == mainGameHierarchy);
  nusmv_assert(NODE_LIST(NULL) == stored_dependent);
  nusmv_assert(NODE_LIST(NULL) == stored_specific);
  set_pgm_name(OptsHandler_create(), PACKAGE_NAME); //NEW
  Game_init_opt();
  Game_init_cmd();
  game_pkg_add_cmds(Game_cmd_get_generic_commands());

  { /* walkers */
    MasterPrinter_ptr mp = node_pkg_get_global_master_wff_printer();
    MasterPrinter_ptr msp = node_pkg_get_global_master_sexp_printer();
    TypeChecker_ptr tc =
      SymbTable_get_type_checker(Compile_get_global_symb_table());

    CATCH {
      NodeWalker_ptr walker;

      walker = NODE_WALKER(PrinterGame_create("GAME Printer"));
      MasterNodeWalker_register_walker(MASTER_NODE_WALKER(mp), walker);

      walker = NODE_WALKER(PrinterSexpGame_create("GAME Sexp Printer"));
      MasterNodeWalker_register_walker(MASTER_NODE_WALKER(msp), walker);

      walker = NODE_WALKER(CheckerGame_create());
      MasterNodeWalker_register_walker(MASTER_NODE_WALKER(tc), walker);
    }

    FAIL {
      Game_Quit();
      nusmv_exit(1);
    }
  }
}

/**Function********************************************************************

  Synopsis    [ Quits the game package. ]

  Description [ This is called when stopping and resetting NuGaT. ]

  SideEffects [ ]

  SeeAlso     [ Game_Init, Game_Mode_Exit ]

******************************************************************************/
void Game_Quit(void)
{
  if (opt_verbose_level_gt(OptsHandler_create(), 0)) {
    fprintf(nusmv_stderr, "Quitting the Game package... \n");
  }

  if (opt_game_game(OptsHandler_create())) {
    Game_Mode_Exit();
  }

  game_pkg_remove_cmds(Game_cmd_get_generic_commands());
  Game_quit_cmd();

  nusmv_assert(GAME_HIERARCHY(NULL) == mainGameHierarchy);
  nusmv_assert(NODE_LIST(NULL) == stored_dependent);
  nusmv_assert(NODE_LIST(NULL) == stored_specific);
}

/**Function********************************************************************

  Synopsis    [ Enters game mode. ]

  Description [ Switches property database to game and the command set
                to the commands applicable in game mode. Sets game
                mode option. ]

  SideEffects [ ]

  SeeAlso     [ Game_Mode_Exit, Game_Init ]

******************************************************************************/
void Game_Mode_Enter(void)
{
  nusmv_assert(!opt_game_game(OptsHandler_create()));

  if (!opt_batch(OptsHandler_create())) {
    fprintf(nusmv_stderr, "Entering game mode...\n");
  }

  game_pkg_switch_to_prop_db_game();
  game_pkg_switch_to_game_cmds(Game_cmd_get_generic_commands(),
                               Game_cmd_get_dependent_commands(),
                               Game_cmd_get_specific_commands());
  set_game_game(OptsHandler_create());

  if (!opt_batch(OptsHandler_create())) {
    fprintf(nusmv_stderr,
            "Done entering game mode.\n"
            "Note that now game commands apply.\n");
  }
}

/**Function********************************************************************

  Synopsis    [ Exits game mode. ]

  Description [ Destroys mainGameHierarchy. Switches property database
                to standard and the command set to the commands
                applicable in standard mode. Unsets game mode
                option. ]

  SideEffects [ ]

  SeeAlso     [ Game_Mode_Enter, Game_Quit ]

******************************************************************************/
void Game_Mode_Exit(void)
{
  nusmv_assert(opt_game_game(OptsHandler_create()));

  if (!opt_batch(OptsHandler_create())) {
    fprintf(nusmv_stderr, "Exiting game mode...\n");
  }

  if (GAME_HIERARCHY(NULL) != mainGameHierarchy) {
    GameHierarchy_destroy(mainGameHierarchy);
    mainGameHierarchy = GAME_HIERARCHY(NULL);
  }
  game_pkg_switch_to_prop_db();
  game_pkg_switch_from_game_cmds(Game_cmd_get_dependent_commands(),
                                 Game_cmd_get_specific_commands());
  unset_game_game(OptsHandler_create());

  if (!opt_batch(OptsHandler_create())) {
    fprintf(nusmv_stderr,
            "Done exiting game mode.\n"
            "Note that now the commands from before entering game mode "
            "apply.\n");
  }
}

/*---------------------------------------------------------------------------*/
/* Definition of static functions                                            */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [ Switches property database to PropDbGame. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ Game_Mode_Enter, game_pkg_switch_to_prop_db ]

******************************************************************************/
static void game_pkg_switch_to_prop_db_game()
{
  PropDb_ptr db;
  PropDbGame_ptr dbg;

  db = PropPkg_get_prop_database();
  if (db != PROP_DB(NULL)) {
    PropDb_destroy(db);
  }
  dbg = PropDbGame_create();
  PropPkg_set_prop_database(PROP_DB(dbg));
}

/**Function********************************************************************

  Synopsis    [ Switches property database to PropDb. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ Game_Mode_Exit, game_pkg_switch_to_prop_db_game ]

******************************************************************************/
static void game_pkg_switch_to_prop_db()
{
  PropDbGame_ptr dbg;
  PropDb_ptr db;

  dbg = PROP_DB_GAME(PropPkg_get_prop_database());
  if (dbg != PROP_DB_GAME(NULL)) {
    PropDbGame_destroy(dbg);
  }
  db = PropDb_create();
  PropPkg_set_prop_database(db);
}

/*---------------------------------------------------------------------------*/
/* Functions below are independent of game. We use mode1 for
   "non-game" and mode2 for "game".
*/
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [ Switches command set from mode1 to mode2. ]

  Description [ Commands are treated according to four classes:

                1. Generic commands apply in mode1 and mode2
                   alike. They are not touched. This is a fixed list
                   of commands.

                2. Dependent commands apply in mode1 and mode2, but in
                   different ways. They are overloaded in the command
                   table with mode2-specific implementations. Mode1
                   implementations are saved for later restore. This
                   is a fixed list of commands.

                3. Mode1-specific commands don't apply in mode2. They
                   are removed from the command table but saved for
                   later restore. These are commands available upon
                   entering this function and not in 1. or 2.

                4. Mode2-specific commands apply only in mode2. They
                   are added to the command table. This is a fixed
                   list of commands.

                Note that saving/restoring commands only works once,
                i.e., we don't maintain a stack. ]

  SideEffects [ ]

  SeeAlso     [ Game_Mode_Enter, game_pkg_switch_from_game_cmds ]

******************************************************************************/
static void game_pkg_switch_to_game_cmds(NodeList_ptr generic,
                                         NodeList_ptr dependent,
                                         NodeList_ptr specific)
{
  Set_t names_generic_set;
  Set_t names_dependent_set;
  Set_t names_gen_dep_set;
  Set_t names_specific_set;

  nusmv_assert(generic != NODE_LIST(NULL));
  nusmv_assert(dependent != NODE_LIST(NULL));
  nusmv_assert(specific != NODE_LIST(NULL));

  /* Fill set of generic command names. */
  {
    ListIter_ptr iter;

    names_generic_set = Set_MakeEmpty();

    NODE_LIST_FOREACH(generic, iter) {
      CommandDescr_t* descr;

      descr = (CommandDescr_t*) NodeList_get_elem_at(generic, iter);
      names_generic_set =
        Set_AddMember(names_generic_set,
                      (Set_Element_t) find_string((char*) descr->name));
    }
  }

  /* Fill set of dependent command names. */
  {
    ListIter_ptr iter;

    names_dependent_set = Set_MakeEmpty();

    NODE_LIST_FOREACH(dependent, iter) {
      CommandDescr_t* descr;

      descr = (CommandDescr_t*) NodeList_get_elem_at(dependent, iter);
      names_dependent_set =
        Set_AddMember(names_dependent_set,
                      (Set_Element_t) find_string((char*) descr->name));
    }
  }

  /* Form union of generic and dependent command names. */
  {
    names_gen_dep_set = Set_MakeEmpty();
    names_gen_dep_set = Set_Union(names_gen_dep_set, names_generic_set);
    names_gen_dep_set = Set_Union(names_gen_dep_set, names_dependent_set);

    /* names_generic and names_dependent should be disjoint. */
    nusmv_assert(Set_GiveCardinality(names_gen_dep_set) ==
                 Set_GiveCardinality(names_generic_set) +
                 Set_GiveCardinality(names_dependent_set));
  }

  /* Find command names that are neither generic nor dependent, i.e.,
     mode1-specific. */
  {
    avl_generator* gen;
    char* key;

    names_specific_set = Set_MakeEmpty();
    avl_foreach_item(cmdCommandTable, gen, AVL_FORWARD, &key, (char**) NULL) {
      if (!Set_IsMember(names_gen_dep_set, (Set_Element_t) find_string(key))) {
        names_specific_set = Set_AddMember(names_specific_set,
                                           (Set_Element_t) find_string(key));
      }
    }
  }

  /* Store and remove mode1 versions of dependent commands. */
  {
    Set_Iterator_t iter;

    nusmv_assert(stored_dependent == NODE_LIST(NULL));
    stored_dependent = NodeList_create();
    SET_FOREACH(names_dependent_set, iter) {
      string_ptr name = (string_ptr) Set_GetMember(names_dependent_set, iter);
      game_pkg_store_remove_cmd(get_text(name), stored_dependent);
    }
  }

  /* Add mode2 versions of dependent commands. */
  game_pkg_add_cmds(dependent);

  /* Store and remove mode1-specific commands. */
  {
    Set_Iterator_t iter;

    nusmv_assert(stored_specific == NODE_LIST(NULL));
    stored_specific = NodeList_create();
    SET_FOREACH(names_specific_set, iter) {
      string_ptr name = (string_ptr) Set_GetMember(names_specific_set, iter);
      game_pkg_store_remove_cmd(get_text(name), stored_specific);
    }
  }

  /* Add mode2-specific commands. */
  game_pkg_add_cmds(specific);

  /* Destroy names_*_set. */
  Set_ReleaseSet(names_specific_set);
  Set_ReleaseSet(names_gen_dep_set);
  Set_ReleaseSet(names_dependent_set);
  Set_ReleaseSet(names_generic_set);
}

/**Function********************************************************************

  Synopsis    [ Switches command set from mode2 to mode1. ]

  Description [ Commands are treated according to four classes:

                1. Generic commands apply in mode1 and mode2 mode
                   alike. They are not touched. This is a fixed list
                   of commands.

                2. Dependent commands apply in mode1 and mode2, but in
                   different ways. They are overloaded in the command
                   table with their respective mode1 implementations
                   as of before executing
                   game_pkg_switch_to_game_cmds. This is a fixed list
                   of commands.

                3. Mode1-specific commands don't apply in mode2. They
                   are restored in the command table as they were
                   before executing game_pkg_switch_to_game_cmds.

                4. Mode2-specific commands apply only in mode2. They
                   are removed from the command table. This is a fixed
                   list of commands.

                Note that saving/restoring commands only works once,
                i.e., we don't maintain a stack. ]

  SideEffects [ ]

  SeeAlso     [ Game_Mode_Exit, game_pkg_switch_to_game_cmds ]

******************************************************************************/
static void game_pkg_switch_from_game_cmds(NodeList_ptr dependent,
                                           NodeList_ptr specific)
{
  nusmv_assert(dependent != NODE_LIST(NULL));
  nusmv_assert(specific != NODE_LIST(NULL));

  /* Remove game-specific commands. */
  game_pkg_remove_cmds(specific);

  /* Restore (non-game)-specific commands. */
  game_pkg_restore_cmds(&stored_specific);

  /* Remove game-versions of dependent commands. */
  game_pkg_remove_cmds(dependent);

  /* Restore (non-game)-versions of dependent commands. */
  game_pkg_restore_cmds(&stored_dependent);
}

/**Function********************************************************************

  Synopsis    [ Adds commands in 'commands' whose command_fp is not NULL
                to the command table. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ game_pkg_remove_cmds ]

******************************************************************************/
static void game_pkg_add_cmds(NodeList_ptr commands)
{
  ListIter_ptr iter;

  nusmv_assert(commands != NODE_LIST(NULL));

  NODE_LIST_FOREACH(commands, iter) {
    CommandDescr_t* descr;

    descr = (CommandDescr_t*) NodeList_get_elem_at(commands, iter);
    if (descr->command_fp != (PFI) NULL) {
      nusmv_assert(!Cmd_CommandDefined(descr->name));
      Cmd_CommandAdd(descr->name,
                     descr->command_fp,
                     descr->changes_hmgr,
                     descr->reentrant);
      nusmv_assert(Cmd_CommandDefined(descr->name));
    }
  }
}

/**Function********************************************************************

  Synopsis    [ Removes commands in 'commands' whose command_fp is not
                NULL from the command table. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ game_pkg_remove_cmds ]

******************************************************************************/
void game_pkg_remove_cmds(NodeList_ptr commands)
{
  ListIter_ptr iter;

  nusmv_assert(commands != NODE_LIST(NULL));

  NODE_LIST_FOREACH(commands, iter) {
    CommandDescr_t* descr;

    descr = (CommandDescr_t*) NodeList_get_elem_at(commands, iter);
    if (descr->command_fp != (PFI) NULL) {
      nusmv_assert(Cmd_CommandDefined(descr->name));
      Cmd_CommandRemove(descr->name);
      nusmv_assert(!Cmd_CommandDefined(descr->name));
    }
  }
}

/**Function********************************************************************

  Synopsis    [ Stores and removes the command 'name' in the command table. ]

  Description [ An assumed-to-be-existing command 'name' from the
                command table is stored in 'stored' and then removed
                from the command table. ]

  SideEffects [ ]

  SeeAlso     [ game_pkg_switch_to_game_cmds ]

******************************************************************************/
static void game_pkg_store_remove_cmd(char* name, NodeList_ptr stored)
{
  CommandDescr_t* descr;

  nusmv_assert(name != (char*) NULL);
  nusmv_assert(stored != NODE_LIST(NULL));
  nusmv_assert(Cmd_CommandDefined(name));

  descr = Cmd_CommandGet(name);
  NodeList_append(stored, (node_ptr) CmdCommandCopy(descr));
  Cmd_CommandRemove(name);
}

/**Function********************************************************************

  Synopsis    [ Restores the commands in stored. ]

  Description [ Adds each command in '*stored' to the command table
                and then frees elements of and list proper
                '*stored'. Commands in '*stored' must not yet be in
                command table. ]

  SideEffects [ ]

  SeeAlso     [ game_pkg_switch_from_game_cmds ]

******************************************************************************/
static void game_pkg_restore_cmds(NodeList_ptr* stored)
{
  nusmv_assert(stored != (NodeList_ptr*) NULL);
  nusmv_assert(*stored != NODE_LIST(NULL));

  while (NodeList_get_length(*stored) != 0) {
    ListIter_ptr first;
    CommandDescr_t* descr;

    first = NodeList_get_first_iter(*stored);
    descr = (CommandDescr_t*) NodeList_remove_elem_at(*stored, first);
    nusmv_assert(descr != (CommandDescr_t*) NULL);
    nusmv_assert(!Cmd_CommandDefined(descr->name));
    Cmd_CommandAdd(descr->name,
                   descr->command_fp,
                   descr->changes_hmgr,
                   descr->reentrant);
    CmdCommandFree((char*) descr);
  }
  NodeList_destroy(*stored);
  *stored = NODE_LIST(NULL);
}

/**AutomaticEnd***************************************************************/
