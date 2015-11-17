================================================================================
MIGRATION FROM NuGAT 0.5.4 (NuSMV 2.5.4)to NuGAT 0.6.0 (NuGAT 2.6.0)

October 2015

Lorenzo Dibenedetto - lorenzodibenedetto90@gmail.com
Sebastian Sardina - ssardina@gmail.com 
Nitin Yadav - nitin.yadav@rmit.edu.au

================================================================================

1.Fatal Error: nusmv-2.pc: No such file or directory

    *   added new folder 'nusmv-config' with  'nusmv-config/nusmv-2.pc' file
    *   modified 'configure' and 'configure.ac' file with 'nusmv_config_dir=nusmv-config' for nusmv-2.pc and removed the helper -> "$nusmv_dir/libnusmv.la"

2.Fatal Error: {several files} : No such file or directory 

    *   replaced all path "$(NUSMV_DIR)/src" with "$(NUSMV_DIR)/code/nusmv/core" and "$(nusmv_dir)/src" with "$(nusmv_dir)/code/nusmv/core"
    *   added all path in all Makefile(.am and .in) that contain $(NUSMV_DIR) with $(NUSMV_DIR)/code/nusmv/core $(NUSMV_DIR)/code/nusmv/shell -I$(NUSMV_DIR)/code/nusmv -I$(NUSMV_DIR)/code -I$(NUSMV_DIR)/build/code -I$(NUSMV_DIR)/build

3.Fatal Error: cudd/util.h: No such file or directory

    *   check if exists the directory "include" into 'NuSMV-2.6.0/cudd-2.4.1.1', if not present execute 'setup.sh' into NuSMV-2.6.0/cudd-2.4.1.1 directory

4.error: statement EXTERN is missing 
    
    *   added this 2 lines in config.h.in
    
            /* Define to 1 if the system has EXTERN and ARGS */
            #define HAVE_EXTERN_ARGS_MACROS 1

5.warning: ggrammar.y:1076:38: warning: passing argument 1 of ‘opt_game_game’ makes pointer from integer without a cast
                        if (!opt_game_game(OptsHandler_get_instance())) {...

    *   This is because NuSMV has renamed  OptsHandler_get_instance with OptsHandler_create
    *   Rename all calls to OptsHandler_get_instance with OptsHandler_create in NuGat code.

6.warning: macro ...  
    .1 "new_node" requires 4 arguments, but only 3 given -> added 'nodemgr' parameter
    .2 "cons" requires 3 arguments, but only 2 given -> added 'nodemgr' parameter
    .3 "new_lined_node" requires 5 arguments, but only 4 given -> added 'nodemgr' parameter
    .4 "find_node" requires ... -> added 'nodemgr' parameter
    .5 "print_node" requires ... -> added 'wffprint' parameter
    .6 "free_node" requires ... -> added 'nodemgr' parameter
    .7 "sprint_node" requires ... -> added 'wffprint' parameter
    .8 "Wff2Nnf","CompileFlatten_hash_module" requires ... -> added 'env' parameter
    
    *   added this lines before the usage 
    
            const NuSMVEnv_ptr env = EnvObject_get_environment(ENV_OBJECT(self));
            const NodeMgr_ptr nodemgr = NODE_MGR(NuSMVEnv_get_value(env, ENV_NODE_MGR));
            MasterPrinter_ptr wffprint = MASTER_PRINTER(NuSMVEnv_get_value(env, ENV_WFF_PRINTER));

7.warning: grammar.y.: implicit declaration of function ‘yylex’,‘yyerror’ and ‘yyerror_lined’

     *   change in parser/Makefile(.am and .in)
        
            **  the flags
                AM_YFLAGS = -d -p nusmv_yy
                AM_LFLAGS = -l -Pnusmv_yy

    *   replace in grammar.y.2.55 'yyerror_lined' with 'nusmv_yyerror_lined'
        
8.error: grammar.y : function 'find_string' not found

    *   'find_string(' has been replaced 
    
            by 'UStringMgr_find_string(strings,' with 'strings' declaration 'UStringMgr_ptr strings = USTRING_MGR(NuSMVEnv_get_value(env, ENV_STRING_MGR));'
            
            and in grammar.y.2.55 with 'UStringMgr_find_string(USTRING_MGR(NuSMVEnv_get_value(__nusmv_parser_env__, ENV_STRING_MGR)),'
            
        
9.error : input.l: ‘nusmv_yytext’ undeclared (first use in this function) ------------- ^"#"" "[0-9]+.*\n       sscanf(nusmv_yytext,"# %d",&nusmv_yylineno); 
            
    *   added this variable after 'AM_LFLAGS' in the parser/Makefile(.am and .in)
        
            LEX_OUTPUT_ROOT = lex.nusmv_yy
       
10.error: input.l : ‘yylval’ undeclared (first use in this function)

    *   replaced in input.2.55 the string 'yylval' with 'nusmv_yylval' and 'yylineno' with 'nusmv_yylineno'

11.error: input.l : ‘TOK_GAME’ undeclared (first use in this function) 

    *   added a new file parser/input.l.1.55 with '#include "grammar.h"' 
    *   included this file (input.l.1.55) in parser/Makefile(.am and .in) after input.l.1.50
    *   added 'src/parser/input.l.1.55' in CMakeList.txt

12.error: gameOpt.c : too few arguments to function ‘OptsHandler_register_option’

    *   added argument to Game_init_opt(NuSMVEnv_ptr const env) in gameInt.h and gameOpt.c 
    *   in gamePkg.c
            -added in head 'NuSMVEnv_ptr env = NuSMVEnv_create();' and update 'Game_init_opt();' with 'Game_init_opt(env);' in 'void Game_Init(void)'
            -append these 2 libraries
            
                    #include "nusmv/core/utils/StreamMgr.h"
                    #include "nusmv/core/cinit/NuSMVEnv.h"
                   
13.error: GamePlayer.c : ‘USTRING_MGR’ undeclared (first use in this function)

    *   'USTRING_MGR' has been replaced by 'USTRING_MGR(NuSMVEnv_get_value(__nusmv_parser_env__, ENV_STRING_MGR))'
    *   added this line below the #include code
            
            extern NuSMVEnv_ptr __nusmv_parser_env__;
    
14.warning: GameStrategy.c : passing argument 1 of ‘bdd_free’ from incompatible pointer type

    *   replaced 'DdManager*'/'DdManager *' with 'DDMgr_ptr' in all files

15.warning: GameStrategy.c : implicit declaration of function ‘Enc_get_bdd_encoding’

    *   is replaced with: if 'fsm' variable is 
        -present 
        
                BddFsm_get_bdd_encoding(BDD_FSM(fsm))
                BddFsm_get_bdd_encoding(BDD_FSM(scalar_fsm)) 
                BddFsm_get_bdd_encoding(BDD_FSM(bool_fsm)) ('enc' and 'st' dropped below the 'bool_fsm' declaration)
                
        -not present
                
                BddFsm_get_bdd_encoding(BDD_FSM(GAME_BDD_FSM(NULL)));
                BddFsm_get_bdd_encoding(BDD_FSM(GAME_SEXP_FSM(NULL)));
                
16.warning: GameStrategy.c: passing argument 1 of ‘print_node’ from incompatible pointer type
   
    *   replace print_node(...) with print_node(wffprint,...)
        replaced SymbType_print(...) with SymbType_print(... , wffprint , ...)
           
        changed this functions in GameStrategy.c and gameCheckLTLSF07.c
              
           -added this lines in head of GameStrategy_print_module() 
                   
                   env = EnvObject_get_environment(ENV_OBJECT(st));
                   MasterPrinter_ptr wffprint = MASTER_PRINTER(NuSMVEnv_get_value(env, ENV_WFF_PRINTER));
   
   
        changed this functions in smgameMain.c
   
           main()
                   -insert in head
                           
                           NuSMVEnv_ptr env = NuSMVEnv_create();
                       
                   -added first parameter 'env'
   
                          NuSMVCore_init(env,...)
                          NuSMVCore_init_cmd_options(env)
                          sm_ParseLineOptions(env,...)
                          Cmd_CommandExecute(env,...)
          
           UsagePrint()
   
                   -added first parameter 'env'
                   
                           UsagePrint(const NuSMVEnv_ptr env,...)
                           get_preprocessors_num(env,...)
                           get_preprocessor_names(env,...)
                           
           sm_ParseLineOptions()
           
                   -added parameter 'env'
                           
                           sm_ParseLineOptions(const NuSMVEnv_ptr env,...)
                           set_pp_list(...,env)
                           UsagePrint(env,...)
                           

17.warning: GameStrategy.c: passing argument 7 of ‘BddEnc_print_bdd_wff’ from incompatible pointer type

    *   replaced the parameter "out" with "OSTREAM(out)"

18.warning: gameCmd.c:  initialization from incompatible pointer type {"read_rat_file",        CommandReadRatFile, 0, true},

    *   added the "NuSMVEnv_ptr env" parameter in functions declaration
        
            static int Command...(NuSMVEnv_ptr env,...)

19.error: gameCmd.c:  ‘nusmv_stderr’ undeclared (first use in this function) 

    *   replaced 'nusmv_stdout' with 'stdout' and 'nusmv_stderr' with 'stderr'
    
20.warning: gameCmd.c:  implicit declaration of function ‘nusmv_exit’ 

    *   replaced all 'nusmv_exit' with 'exit'
    *   added this line in head where 'env' is added
    
            const NuSMVEnv_ptr env = EnvObject_get_environment(ENV_OBJECT(...));
                    
    *   added as first parameter "env" to :
            
            Compile_check_if_flattening_was_built
            Compile_check_if_encoding_was_built
            Compile_check_if_model_was_built
            Compile_check_if_bool_model_was_built
            Compile_check_if_flattening_was_built
            CmdOpenPipe
            CmdOpenFile

21.error: gameCmd.c:  ‘CATCH’ undeclared (first use in this function)
                         
    *   replaced "CATCH" with "CATCH(errmgr)" and "FAIL" with "FAIL(errmgr)" and added this lines of declaration
    
            NuSMVEnv_ptr const env = EnvObject_get_environment(ENV_OBJECT(self->symb_table));  ( ONLY IF 'env' IS NOT DECLARED )
            ErrorMgr_ptr const errmgr = ERROR_MGR(NuSMVEnv_get_value(env, ENV_ERROR_MANAGER));
                        
22.warning: gameCmd.c: implicit declaration of function ‘PropPkg_get_prop_database’

    *   replaced with variable "prop_db" and declaration
    
            PropDb_ptr prop_db  = PROP_DB(NuSMVEnv_get_value(env, ENV_PROP_DB));
            
23.error: gameCmd.c: ‘USTRING_MGR’ undeclared (first use in this function)

    *   *   'USTRING_MGR' has been replaced by 'USTRING_MGR(NuSMVEnv_get_value(env, ENV_STRING_MGR))'
    
24.warning: gameCmd.c:  passing argument 2 of ‘PropDb_print_list_header’ from incompatible pointer type

    *   added "OStream_ptr ostream_ptr_nusmv_output = OStream_create(nusmv_stdout);" before the 'PropDb_print_list_header()' function
    *   replaced for :
            'PropDb_print_list_header()' and 'PropDb_print_prop_at_index()' -> 'nusmv_output' with 'ostream_ptr_nusmv_output'
            
25.error: gameCmd.c:  ‘dd_manager’ undeclared (first use in this function)

    *   added declaration "DDMgr_ptr dd_manager = (DDMgr_ptr )NuSMVEnv_get_value(env, ENV_DD_MGR);"
    
26.warning: gamePkg.c: implicit declaration of function

    *   all this functions are replaced
    
            ‘node_pkg_get_global_master_wff_printer’ with 'MASTER_PRINTER(NuSMVEnv_get_value(env, ENV_WFF_PRINTER))'
            ‘node_pkg_get_global_master_sexp_printer’ with 'MASTER_PRINTER(NuSMVEnv_get_value(env, ENV_SEXP_PRINTER));'
            ‘Compile_get_global_symb_table’ with 'symb_table'
            ‘PropPkg_get_prop_database’ with 'PROP_DB(NuSMVEnv_get_value(env, ENV_PROP_DB));'
                added 'env' parameter for :
                    'game_pkg_switch_to_prop_db_game'
                    'Game_Mode_Enter'
                    'Game_Mode_Exit'
                    'Game_Quit'
                    'Game_CommandWriteBooleanModel'
                    'Game_CommandFlattenHierarchy'
                    'Game_CommandBuildFlatModel'
                    'Game_CommandBuildBooleanModel'
                    'Game_CommandBuildBddModel'
                    'Game_CommandWriteFlatModel'
                    'Game_CommandWriteBooleanModel'
                    'PropDb_create'
                    'CompileFlatten_quit_flattener'
                    'Game_CheckGenReactivitySpec'
                    'command_function_ptr'
                    
            'PropPkg_set_prop_database(PROP_DB(dbg))' with 'NuSMVEnv_set_value(env, ENV_PROP_DB,PROP_DB(dbg))'
    
27.error: gamePkg.c: ‘cmdCommandTable’ undeclared (first use in this function)
    
        *   replaced with 'commandTable' and added declaration 'avl_tree* commandTable = (avl_tree*)NuSMVEnv_get_value(env, ENV_CMD_COMMAND_TABLE);'
        
28.warning: gamePkg.c: implicit declaration of function ‘get_text(’

        *   replaced with '(char*)UStringMgr_get_string_text('
        
        warning: cast to pointer from integer of different size
        
            *   removed '(char*)'

29.warning: gamePkg.c: passing argument 1 of ‘Cmd_CommandDefined’ from incompatible pointer type

        *   added 'env' parameter for : 
        
                'Cmd_CommandDefined'
                'Cmd_CommandAdd'
                'Cmd_CommandRemove'
                'Cmd_CommandGet'
                'NuGaTAddons_Quit'
                
                'game_pkg_switch_from_game_cmds'
                'game_pkg_add_cmds'
                'game_pkg_remove_cmds'
                'game_pkg_store_remove_cmd'
                'game_pkg_restore_cmds'
                
                'CommandGameReset'
                'Smgame_Init'
                'Smgame_AddCmd'
                'Smgame_Reset'
                'Smgame_End'
            
30.warning: gameGeneral.c: implicit declaration of function ‘PropDb_set_fsm_to_master’

    *   replaced 'PropDb_set_fsm_to_master(..., PROP(self->prop));' with 'Prop_set_environment_fsms(env, PROP(self->prop));'

31.warning: gameGeneral.c: implicit declaration of function ‘internal_error(’ 

    *   replaced with 'ErrorMgr_internal_error(errmgr,'
    *   added library '#include "utils/ErrorMgr.h"'
    *   added 'env' parameter to:
            
            'Game_AfterCheckingSpec'
            'Game_UseStrongReachabilityAlgorithm'
            'PrinterGame_create'
            'PrinterSexpGame_create'
            'PrinterGame_create'
            'printer_base_init'
            
32.warning: gameGeneral.c: passing argument 1 of ‘SymbLayer_gen_iter’ and 'SymbLayer_iter_to_list’ from incompatible pointer type

    *   removed '&' for the first parameter
    
33.warning: gameGeneral.c:  passing argument 2 of ‘Prop_print’ from incompatible pointer type

    *   added cast of the second argument with '(OStream_ptr)...'      
            
34.warning: gameFlatten.c: implicit declaration of function ‘Compile_get_global_symb_table’

    *   replaced with 'SYMB_TABLE(NuSMVEnv_get_value(env, ENV_SYMB_TABLE))'
    *   added 'env' parameter for :
            'game_declare_special_var'
            'game_undeclare_special_var'
            'Game_SF07_StructCheckLTLGameSF07_create'
            'Game_CheckLtlGameSpecSF07'
            'game_check_first_player_recur'
            'game_check_first_player'
            'Game_UnrealizableCore_Struct_create'
            'Game_CheckGameSpecAndComputeCores'
            
35.error: gameFlatten.c: too few arguments to function ‘CompileFlatten_init_flattener’ &&
   warning: passing argument 1 of ‘sym_intern’ from incompatible pointer type
   warning: passing argument 1 of ‘Compile_ConstructHierarchy’ from incompatible pointer type

    *   added 'env' parameter
    
36.warning: passing argument 1 of ‘Compile_ConstructHierarchy’ from incompatible pointer type [ TODO : CHECK IF IT IS CORRECT ]

    *   added parameter 'boolean expand_bounded_arrays = false;'    
    
37.warning: implicit declaration of function ‘rpterr’

    *   replaced with 'ErrorMgr_rpterr(errmgr,' and added declaration when required 'const ErrorMgr_ptr errmgr = ERROR_MGR(NuSMVEnv_get_value(env, ENV_ERROR_MANAGER));'
    *   added 'env' parameter for:
            'GameSexpFsm_create'
            'game_construct_game_fsms'
            'game_is_opponent_constraint_minimal'
            'game_compute_core_using_parameters'
            
38.warning: implicit declaration of function ‘error_game_definition_contains_input_vars’

    *   replaced with 'ErrorMgr_error_game_definition_contains_input_vars(errmgr,' 
    *   added declaration when required 'const ErrorMgr_ptr errmgr = ERROR_MGR(NuSMVEnv_get_value(env, ENV_ERROR_MANAGER));'
    *   added 'env' parameter for 'Compile_ProcessHierarchy'
    *   added 'nodemgr' parameter for 'PslNode_new_context'
    
39.warning: comparison between pointer and integer 'sym_intern(env,((car(spec)) == 1 ?'

    *   added a cast with '(node_ptr)'
    
40.warning: implicit declaration of function ‘error_second_player_next_var’

    *   replaced with 'ErrorMgr_error_second_player_next_var (errmgr,'
    *   replaced 'error_second_player_var' with 'ErrorMgr_error_second_player_var(errmgr,'
    *   added declaration when required 'const ErrorMgr_ptr errmgr = ERROR_MGR(NuSMVEnv_get_value(env, ENV_ERROR_MANAGER));'
    
41.error: gameFlatten.c: ‘yylineno’  undeclared (first use in this function)

    *   replaced with 'nusmv_yylineno'

42.error: gameVarEncoding.c:111:65: ‘self’ undeclared (first use in this function)

    *   added 'env' parameter for 'Game_CommandEncodeVariables'
    *   removed 'env' declaration inside the function 

43.error: too few arguments to function ‘Enc_init_bool_encoding’

    *   added 'env' parameter for :
            
            'Enc_init_bool_encoding'
            'Enc_init_bdd_encoding'
            
44.warning: implicit declaration of function ‘Enc_get_bool_encoding()’

    *   replaced with 'BoolEncClient_get_bool_enc(BOOL_ENC_CLIENT(ARG))'
        ARG is replaced with : 
        
            'enc' in gameBuildModel.c   
            'NULL' in gameCheckGenReactivityBuchiSpec.c and gameUnrealCore.c
            'bdd_enc' in gameVarEncoding.c and swapped the code
            
45.error: too few arguments to function ‘Enc_init_bdd_encoding’

    *   added second parameter 'input_order_file_name'

46.warning: passing argument 1 of ‘Compile_WriteFlattenFsm’ from incompatible pointer type
   warning: passing argument 1 of ‘Compile_WriteBoolFsm’ from incompatible pointer type
        
    *   added 'env' parameter
        
47.warning: passing argument 1 of ‘BoolEnc_scalar_layer_to_bool_layer’ from incompatible pointer type

    *   added first parameter 'BoolEnc_ptr bool_enc = BOOL_ENC(NuSMVEnv_get_value(env, ENV_BOOL_ENCODER));'

48.errors and warnings in gameXmlReader.c 
    
    warning: implicit declaration of function ‘error_out_of_memory’
    
        *    replaced with 'ErrorMgr_error_out_of_memory(errmgr,' and added 'errmgr' parameter to 'gameXmlReader_XmlParseResult_create'
    
    error: 317:9 : assignment of read-only variable ‘env’
    
        *   passed as parameter and changed declaration 
        
49.warning: gameXmlReader.c: passing argument 2 of ‘XML_SetElementHandler’ from incompatible pointer type

    *   remove 'env' parameter and added inside each function
    *   added 'env; parameter for :
            'Parser_read_psl_from_string'
            'PslNode_convert_psl_to_core'
            
50.gameUnrealCore.c

    warning: passing argument 1 of ‘SymbType_create’ makes pointer from integer without a cast
    
        *   added 'env' parameter
    
    error: macro "find_atom" requires 2 arguments
            
        *   added 'nodemgr' parameter
    
    warning: passing argument 7 of ‘BddEnc_print_bdd_wff’ from incompatible pointer type
    
        *   add cast '(OStream_ptr)' to 'nusmv_stdout' parameter
        
    warning: passing argument 8 of ‘game_minimize_players_constraints’ from incompatible pointer type
    
        *   add cast '(game_is_game_still_correct)' to 'game_is_opponent_constraint_minimal' parameter
        
51.gameCheckLTLSF07.c  

    warning: implicit declaration of function ‘w2w_init_wff2nnf()’ and ‘w2w_quit_wff2nnf()’
    
        *   replaced with 'wff_pkg_init(env)' and 'wff_pkg_quit(env)'
        
    warning: passing argument 1 of ‘Compile_FlattenHierarchy’ from incompatible pointer type
    
        *   added 'env' and new parameter 'expand_bounded_arrays' with 'false' (default value)

52.PropGame.c

    error: too few arguments to function ‘prop_init’
    
        *   added env parameter for all the function until 'prop_db_game_prop_create_and_add' that is the highest level with 'env' declaration inside
        
    warning: implicit declaration of function ‘indent’ and ‘indent_node’
    
        *   replaced
        
                'indent(file)'  with 
                
                        for(i=0; i < OStream_get_indent_size(OSTREAM(file)); i++) fprintf(file, "  ");
            
                'indent_node(file, "", p, " ");'  with 
                        
                        for(i=0; i < OStream_get_indent_size(OSTREAM(file)); i++) fprintf(file, "  ");
                        fprintf(file, "%s", "");
                        print_node(wffprint,file, p);
                        fprintf(file, "%s", " ");
                        
53.PropDbGame.c [ TODO : find solution for commented line ]
    
    warning: passing argument 2 of ‘Prop_print_db’ from incompatible pointer type
    
        *   add cast with 'OSTREAM(file)'
        
    error: ‘struct PropDb_TAG’ has no member named ‘master’ "prop = PROP_GAME(PROP_DB(self)->master);" 
    
        *   replaced 'PROP_DB(self)->master' with 'NuSMVEnv_get_value(env, ENV_PROP_DB)'
        *   replaced 'PROP_DB(self)->master = PROP(PropGame_create(env))' with 'NuSMVEnv_set_value(env, ENV_PROP_DB, PROP(PropGame_create(env)))'
        
        *   commented this line 'OVERRIDE(PropDb, set_fsm_to_master) = (PropDb_set_fsm_to_master_method) prop_db_game_set_fsm_to_master;'
    
    *   added 'env' parameter for 'PropDbGame_create' , 'PropDbGame_clean' , 'prop_db_game_init' , 'prop_db_init'
    
54.walkers/CheckerGame.c

    warning: passing argument 2 of ‘checker_base_init’ from incompatible pointer type 
    
        *   added 'env' parameter for : 'checker_game_init' , 'CheckerGame_create'
        
    error: too few arguments to function ‘SymbTablePkg_error_type’
    
        *   added 'env' parameter for 'SymbTablePkg_error_type'
        
    error: ‘nusmv_stderr’ undeclared (first use in this function)
    
        *   replaced with 'stderr'
        
55.src/addons/addons.h
    
    fatal error: util.h: No such file or directory  '#include "util.h"'

        *   removed line because 'util.h' is not present
        
56.smgameMisc.c

    warning: implicit declaration of function ‘util_resetlongjmp()’
    
        *   replaced with 'ErrorMgr_reset_long_jmp(errmgr)'
        
    warning: passing argument 1 of ‘Cmd_CommandExecute’ from incompatible pointer type
    
        *   added 'env' parameter
        
    warning: implicit declaration of function ‘PropDb_master_get_bdd_fsm’ [ TODO : CHECK IF CORRECT ]
    
        *   replaced with 'Prop_get_bdd_fsm' (line 478 miss round bracket ) and changed 'PROB_DB' in 'PROB'
        
    warning: passing argument 5 of ‘BddFsm_print_reachable_states_info’ from incompatible pointer type
    
        *   add cast for 'nusmv_stdout' with 'OSTREAM(nusmv_stdout)'
        
================================================================================
EOF
================================================================================
