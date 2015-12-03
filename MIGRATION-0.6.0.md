================================================================================

MIGRATION FROM NuGAT 0.5.4 (NuSMV 2.5.4)to NuGAT 0.6.0 (NuGAT 2.6.0)

October 2015

Lorenzo Dibenedetto - lorenzodibenedetto90@gmail.com , Sebastian Sardina - ssardina@gmail.com , Nitin Yadav - nitin.yadav@rmit.edu.au

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
    
    *   added 'add_definitions(-DHAVE_EXTERN_ARGS_MACROS)' in 'CMakeLists.txt' file
    
5.warning: ggrammar.y:1076:38: warning: passing argument 1 of ‘opt_game_game’ makes pointer from integer without a cast
                        if (!opt_game_game(OptsHandler_get_instance())) {...

    *   replace 'OptsHandler_get_instance' with 'OptsHandler_ptr opts = OPTS_HANDLER(NuSMVEnv_get_value(env, ENV_OPTS_HANDLER));' in NuGat code.

        
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

    *   'USTRING_MGR' has been replaced by 'USTRING_MGR(NuSMVEnv_get_value(env, ENV_STRING_MGR))'
    *   added 'env' parameter 
    
14.warning: GameStrategy.c : passing argument 1 of ‘bdd_free’ from incompatible pointer type

    *   replaced 'DdManager*'/'DdManager *' with 'DDMgr_ptr' in all files

15.warning: GameStrategy.c : implicit declaration of function ‘Enc_get_bdd_encoding’

    *   replaced with 'NuSMVEnv_get_value(env, ENV_BDD_ENCODER);'
        and 'Enc_get_bool_encoding' with 'NuSMVEnv_get_value(env, ENV_BOOL_ENCODER);'
                
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
            ‘Compile_get_global_symb_table’ with 'SYMB_TABLE(NuSMVEnv_get_value(env, ENV_SYMB_TABLE))'
            ‘PropPkg_get_prop_database’ with 'PROP_DB(NuSMVEnv_get_value(env, ENV_PROP_DB));'
            'PropPkg_set_prop_database(PROP_DB(dbg))' with 'NuSMVEnv_set_value(env, ENV_PROP_DB, PROP_DB(dbg))'
            
                added 'env' parameter for :
                    'game_pkg_switch_to_prop_db_game'
                    'Game_Mode_Enter'
                    'Game_Mode_Exit'
                    'Game_Init'
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
                    
27.error: gamePkg.c: ‘cmdCommandTable’ undeclared (first use in this function)
    
        *   replaced with 'commandTable' and added declaration 'avl_tree* commandTable = (avl_tree*)NuSMVEnv_get_value(env, ENV_CMD_COMMAND_TABLE);'
        
28.warning: gamePkg.c: implicit declaration of function ‘get_text(’

        *   replaced with '(char*)UStringMgr_get_string_text('
        *   replaced with 'UStringMgr_get_string_text(' in 'gameUnrealCore.c' for condition statements

29.warning: gamePkg.c: passing argument 1 of ‘Cmd_CommandDefined’ from incompatible pointer type

        *   added 'env' parameter for : 
        
                'Cmd_CommandDefined', 'Cmd_CommandAdd', 'Cmd_CommandRemove' ,'Cmd_CommandGet' 
                
                'NuGaTAddons_Init', 'NuGaTAddons_Quit'
                
                'game_pkg_switch_from_game_cmds', 'game_pkg_add_cmds', 'game_pkg_remove_cmds', 'game_pkg_store_remove_cmd', 'game_pkg_restore_cmds'
                
                'CommandGameReset'
                
                'Smgame_Init', 'Smgame_AddCmd', 'Smgame_Reset', 'Smgame_End','Smgame_BatchMain'
            
30.warning: gameGeneral.c: implicit declaration of function ‘PropDb_set_fsm_to_master’

    *   replaced 'PropDb_set_fsm_to_master(..., PROP(self->prop));' with 'Prop_set_environment_fsms(env, PROP(self->prop));'

31.warning: gameGeneral.c: implicit declaration of function ‘internal_error(’ 

    *   replaced with 'ErrorMgr_internal_error(errmgr,'
    *   added library '#include "utils/ErrorMgr.h"'
    *   added 'env' parameter for :
            
            'Game_AfterCheckingSpec', 'Game_UseStrongReachabilityAlgorithm', 'PrinterGame_create', 'printer_base_init'
            
32.warning: gameGeneral.c: passing argument 1 of ‘SymbLayer_gen_iter’ and 'SymbLayer_iter_to_list’ from incompatible pointer type

    *   removed '&' for the first parameter
    
33.warning: gameGeneral.c:  passing argument 2 of ‘Prop_print’ from incompatible pointer type

    *   added cast of the second argument with '(OStream_ptr)...'      
            
34.warning: gameFlatten.c: implicit declaration of function ‘Compile_get_global_symb_table’

    *   replaced with 'SYMB_TABLE(NuSMVEnv_get_value(env, ENV_SYMB_TABLE))'
    *   added 'env' parameter for :
            'game_declare_special_var', 'game_undeclare_special_var', 'Game_SF07_StructCheckLTLGameSF07_create'
            'Game_CheckLtlGameSpecSF07', 'game_check_first_player_recur', 'game_check_first_player'
            'Game_UnrealizableCore_Struct_create', 'Game_CheckGameSpecAndComputeCores'
            
35.error: gameFlatten.c: too few arguments to function ‘CompileFlatten_init_flattener’
   warning: passing argument 1 of ‘sym_intern’ from incompatible pointer type
   warning: passing argument 1 of ‘Compile_ConstructHierarchy’ from incompatible pointer type

    *   added 'env' parameter
    
36.warning: passing argument 1 of ‘Compile_ConstructHierarchy’ from incompatible pointer type

    gameCmd.c -> CommandGameFlattenHierarchy()
    
        *   added declaration 'boolean expand_bounded_arrays = false;'  because NuSMV2.6.0 uses this new variable 
            which is present is same functions that are used by NuGaT
            
        *   added 'e' option
         
             while( ..."he")) != EOF) {
               ...
                case 'e': expand_bounded_arrays = true; break;
               ...
               }
        
        *   added 'expand_bounded_arrays' parameter for 'Game_CommandFlattenHierarchy()', 'game_flatten_game_hierarchy()'
               
37.warning: implicit declaration of function ‘rpterr’

    *   replaced with 'ErrorMgr_rpterr(errmgr,' and added declaration when required 'const ErrorMgr_ptr errmgr = ERROR_MGR(NuSMVEnv_get_value(env, ENV_ERROR_MANAGER));'
    *   added 'env' parameter for:
            'GameSexpFsm_create', 'game_construct_game_fsms', 'game_is_opponent_constraint_minimal', 'game_compute_core_using_parameters'
            
38.warning: implicit declaration of function ‘error_game_definition_contains_input_vars’

    *   replaced with 'ErrorMgr_error_game_definition_contains_input_vars(errmgr,' 
    *   added 
            declaration when required 'const ErrorMgr_ptr errmgr = ERROR_MGR(NuSMVEnv_get_value(env, ENV_ERROR_MANAGER));'
            parameter 
                'env'  for 'Compile_ProcessHierarchy'
                'nodemgr' for 'PslNode_new_context'
    
39.warning: comparison between pointer and integer 'sym_intern(env,((car(spec)) == 1 ?'

    *   added a cast with '(node_ptr)' for 1 value
    
40.warning: implicit declaration of function ‘error_second_player_next_var’

    *   replaced 
            with 'ErrorMgr_error_second_player_next_var (errmgr,'
            'error_second_player_var' with 'ErrorMgr_error_second_player_var(errmgr,'
    *   added declaration when required 'const ErrorMgr_ptr errmgr = ERROR_MGR(NuSMVEnv_get_value(env, ENV_ERROR_MANAGER));'
    
41.error: gameFlatten.c: ‘yylineno’  undeclared (first use in this function)

    *   replaced with 'nusmv_yylineno'

42.error: gameVarEncoding.c:111:65: ‘self’ undeclared (first use in this function) [ #TOSOLVE the env before ]

    *   added 'env' parameter for 'Game_CommandEncodeVariables'
    *   removed 'env' declaration inside the function 

43.error: too few arguments to function ‘Enc_init_bool_encoding’

    *   added 'env' parameter for :
            
            'Enc_init_bool_encoding', 'Enc_init_bdd_encoding'
            
44.warning: implicit declaration of function ‘Enc_get_bool_encoding()’  [ #CHECK AT RUNTIME ]

    *   replaced with 'NuSMVEnv_get_value(env, ENV_BOOL_ENCODER);'
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

48.gameXmlReader.c 
    
    warning: implicit declaration of function ‘error_out_of_memory’
    
        *   replaced with 'ErrorMgr_error_out_of_memory(errmgr,'
        *   added 'errmgr' parameter to 'gameXmlReader_XmlParseResult_create'
    
    error: 317:9 : assignment of read-only variable ‘env’
    
        *   passed as parameter and changed declaration 
        
49.warning: gameXmlReader.c: passing argument 2 of ‘XML_SetElementHandler’ from incompatible pointer type [#TOSOLVE]

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

    1.warning: implicit declaration of function ‘w2w_init_wff2nnf()’ and ‘w2w_quit_wff2nnf()’
    
        *   replaced with 'NuSMVEnv_get_handled_hash_ptr(env, ENV_W2W_WFF2NNF_HASH);' and 'clear_assoc(NuSMVEnv_get_handled_hash_ptr(env, ENV_W2W_WFF2NNF_HASH));'
            Note: the 'NuSMVEnv_get_handled_hash_ptr' have inside a setter
        
    2.warning: passing argument 1 of ‘Compile_FlattenHierarchy’ from incompatible pointer type
    
        *   added 'env' and new parameter 'expand_bounded_arrays' with 'false' (default value)

52.PropGame.c

    error: too few arguments to function ‘prop_init’
    
        *   added env parameter for all the function until 'prop_db_game_prop_create_and_add' 
                that is the highest level with 'env' declaration inside
        
    warning: implicit declaration of function ‘indent(file)’ and ‘indent_node(file)’
    
        *   replaced
        
                'indent(file)'  with 
                
                        for(i=0; i < OStream_get_indent_size(OSTREAM(file)); i++) fprintf(file, "  ");
            
                'indent_node(file, "", p, " ");'  with 
                        
                        for(i=0; i < OStream_get_indent_size(OSTREAM(file)); i++) fprintf(file, "  ");
                        fprintf(file, "%s", "");
                        print_node(wffprint,file, p);
                        fprintf(file, "%s", " ");
                        
53.PropDbGame.c [ #CHECK .2.3 AT RUNTIME ]
    
    1.warning: passing argument 2 of ‘Prop_print_db’ from incompatible pointer type
    
        *   add cast with 'OSTREAM(file)'
        
    2.error: ‘struct PropDb_TAG’ has no member named ‘master’ "prop = PROP_GAME(PROP_DB(self)->master);" 
    
        *   removed 
                all lines with 'PROP_DB(self)->master' and added 
                'OVERRIDE(PropDb, set_fsm_to_master) = (PropDb_set_fsm_to_master_method) prop_db_game_set_fsm_to_master;'
                prop_db_game_set_fsm_to_master function from PropDbGame.c/PropDbGame_private.h and added in PropGame.c/PropGame_private.h
                    'OVERRIDE(Prop, set_environment_fsms) = (Prop_set_environment_fsms_method) prop_game_set_environment_fsms;' and 
                    'prop_game_set_environment_fsms' function
                    
        *   replaced 
                'if(PropDbGame_master_get_game_bdd_fsm(pdb) != GAME_BDD_FSM(NULL))' with 'if(NuSMVEnv_has_value(env, ENV_BDD_FSM))'
                'PropDbGame_master_set_game_scalar_sexp_fsm(PROP_DB_GAME(NuSMVEnv_get_value(env, ENV_PROP_DB)), scalar_fsm);'   
                    with 'NuSMVEnv_set_value(env, ENV_SEXP_FSM, scalar_fsm);'
                
    3.missing parameter
        
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
        
56.smgameMisc.c [ #CHECK .3 AT RUNTIME ] 

    1.warning: implicit declaration of function ‘util_resetlongjmp()’
    
        *   replaced with 'ErrorMgr_reset_long_jmp(errmgr)'
        
    2.warning: passing argument 1 of ‘Cmd_CommandExecute’ from incompatible pointer type
    
        *   added 'env' parameter
        
    3.warning: implicit declaration of function ‘PropDb_master_get_bdd_fsm(PropPkg_get_prop_database())’ 
    
        *   replaced with 'BDD_FSM(NuSMVEnv_get_value(env, ENV_BDD_FSM))'
        
    4.warning: passing argument 5 of ‘BddFsm_print_reachable_states_info’ from incompatible pointer type
    
        *   added cast for 'nusmv_stdout' with 'OSTREAM(nusmv_stdout)'
        
57.gameCheckLTLSF07_gba_wring.c

    warning: ignoring return value of ‘fgets’, declared with attribute warn_unused_result [-Wunused-result] 'fgets(self->po_s, self->po_size_s, self->output_file);'

        *   added declaration 'char *fgetsResult;' and store the result 'fgetsResult = fgets(...'
     
58.fsm/GameBddFsm.c

    warning: passing argument 2 of ‘BddFsm_print_info’ from incompatible pointer type
    
        *   added cast 'OSTREAM(file)'
        
59.make[3]: *** No rule to make target `/home/lorenzo/Documents/software/ClionProjects/NuSMV-2.6.0/NuSMV/code/nusmv/core/cinit/cinitCmd.lo', needed by `libsmgame.la' 

    *   replaced all 'cinit....lo' with 'cinit....c.o' with a new path
            
            $(NUSMV_DIR)/build/code/nusmv/shell/cinit/CMakeFiles/code_nusmv_shell_cinit.dir/cinitCmd.c.o \
            $(NUSMV_DIR)/build/code/nusmv/core/cinit/CMakeFiles/code_nusmv_core_cinit.dir/cinitInit.c.o \
            $(NUSMV_DIR)/build/code/nusmv/core/cinit/CMakeFiles/code_nusmv_core_cinit.dir/cinitBatch.c.o \
            $(NUSMV_DIR)/build/code/nusmv/core/cinit/CMakeFiles/code_nusmv_core_cinit.dir/cinitVers.c.o \
            $(NUSMV_DIR)/build/code/nusmv/core/cinit/CMakeFiles/code_nusmv_core_cinit.dir/cinitData.c.o
            
    *   removed 
            '$(NUSMV_DIR)/code/nusmv/core/cinit/cinitMisc.lo' line
            'librbcdag.la' library
                
60.src/smgame/smgameMain.c

    error: unknown type name ‘FP_V_V’ , FP_V_V iq_fns[][2] = {{NuGaTAddons_Init, NuGaTAddons_Quit}};
      ^
        *   replaced with 'FP_V_E' because there is 'env' parameter
        
    warning: implicit declaration of function ‘init_options_cmd’
    
        *   replaced with 'Opt_Cmd_init(env)' and added library '#include "opt/optCmd.h"'
        
    warning: implicit declaration of function ‘CInit_NusmvrcSource’
    
        *   replaced with 'Cmd_Misc_NusmvrcSource(env)'

    warning: undefined reference to `nusmv_stderr' ...
    
        *   removed all 'EXTERN ' before declarations
-----------------------------------------------------------------------------------------------------------------      
61.make[2]: *** No rule to make target `/home/lorenzo/Documents/software/ClionProjects/NuSMV-2.6.0/NuSMV/libnusmvcore.la', needed by `NuGaT'.  Stop. 
   make[2]: *** No rule to make target `/home/lorenzo/Documents/software/ClionProjects/NuSMV-2.6.0/NuSMV/librbcdag.la', needed by `NuGaT'.  Stop.
   
   *   replaced with "*.a" files with a new path

            $(NUSMV_DIR)/build/lib/libnusmvshell.a \
            $(NUSMV_DIR)/build/lib/libnusmvaddonscore.a \
            $(NUSMV_DIR)/build/lib/libnusmvcore.a  \
            $(NUSMV_DIR)/build/lib/libnusmvgrammar.a \
            $(NUSMV_DIR)/build/lib/libnusmvrbc.a

62.smgameMain.c  [ TODO : find a solution for variable LIBS ( include in Makefile.am/.in or configure.ac ) ]

    undefined reference to `MMalloc' ... 
    
    *   include cudd library in 'configure.ac' ( copied from NuSMV2.5.4 file 'libnusmvcore.la' )
        S["LIBS"]=" -L/home/lorenzo/Documents/software/ClionProjects/NuSMV-2.6.0/NuSMV/build/build-cudd/lib -lst -lcudd -lepd -lmtr -lutil -lxml2 -lMiniSat -lstdc++ -lreadline -ltermcap /usr/lib/x86_64-linux-gnu/libexpat.la -lm "
        
63.gameCheckLTLSF07.c

        /home/lorenzo/Documents/software/ClionProjects/NuSMV-2.6.0/NuSMV/build/lib/libnusmvcore.a(BddEnc.c.o): In function `BddEnc_dump_expr':
            BddEnc.c:(.text+0x6b82): undefined reference to `log10'
            ...
            
        /home/lorenzo/Documents/software/ClionProjects/NuSMV-2.6.0/NuSMV/build/lib/libnusmvrbc.a(dagStat.c.o): In function `Dag_PrintStats':
        dagStat.c:(.text+0x1d3): undefined reference to `pow'
            
    *   replaced 
            'grep -c "define HAVE_SOLVER_MINISAT 1"' with 'grep -c "define NUSMV_HAVE_SOLVER_MINISAT 1"'
            'yylineno' with 'nusmv_yylineno' in : (resolved 13 rows)
            
                    src/addons/game
                        gameXmlReader.c
                        gameBuildModel.c
                        gameReqToGame.c
            'Sm_BannerPrint_minisat' with 'CInit_BannerPrint_minisat'  (resolved 2 rows)
            'Sm_BannerPrint_zchaff' with 'CInit_BannerPrint_zchaff'  
            
            
    *   included in nusmv-2.pc Minisat library
    
            sat_available=no
            minisat_libdir=/home/lorenzo/Documents/software/ClionProjects/NuSMV-2.6.0/NuSMV/build/build-MiniSat/minisat-37dc6c67e2af26379d88ce349eb9c4c6160e8543
            minisat_libname=MiniSat
            
64.smgameMisc.c:

    warning: passing argument 1 of ‘Bmc_GenSolveLtl’,'Bmc_GenSolveInvar' from incompatible pointer type
        
        *   added 'env' parameter
    
    warning: implicit declaration of function ‘Bmc_check_psl_property’
    
        *   replaced  with 'Bmc_Gen_check_psl_property'
        
    warning: implicit declaration of function ‘set_bmc_mode’,‘set_bmc_pb_length’
  
        *   included library '#include "bmc/bmc.h"'
     
             
65.gameCheckLTLSF07.c : warning: undefined reference to `global_fsm_builder' for :  [ #CHECK AT RUNTIME, ANOTHER DECLARATION ] 
             
     *  replaced 'global_fsm_builder'  with 'FsmBuilder_ptr builder = FSM_BUILDER(NuSMVEnv_get_value(env, ENV_FSM_BUILDER));'
     *  removed all 'global_fsm_builder' declarations
     
66.gameUnrealCore.c : warning: undefined reference to `boolean_range' , 'zero_number' , 'one_number' [ #TODO CHANGE DESCRIPTION ] 
    
    *   replaced with Mgr functions ....

67.grammar.c: warning: implicit declaration of function ‘rpl_malloc’ [ #pending ]

    *   commented line 'AC_FUNC_MALLOC' in 'configure.ac'

68.TraceXmlLoader.c : warning: undefined reference to

     `xmlParseChunk' , `xmlCtxtGetLastError' , `xmlCreatePushParserCtxt' , `xmlFreeParserCtxt'

    *   added '-lxml2' in LIBS variable <configure.ac>
    
69.SatMinisat.c warning: undefined reference to :

       `MiniSat_New_Variable' , `MiniSat_Add_Clause' , `MiniSat_Add_Clause' , `MiniSat_Add_Clause'
       `MiniSat_Add_Clause' , `MiniSat_Add_Clause' , ...
   
    *   added '-lMiniSat' in LIBS variable <configure.ac>
    
70.warning: undefined reference to

    Solver_C.cc for :

        `operator new(unsigned long)' , `operator delete(void*)' , `__cxa_allocate_exception'
        `__cxa_throw' , `operator delete(void*)' , `__cxa_guard_acquire' , `__cxa_guard_release'
  
    SimpSolver.cc for :
      
       `__cxa_allocate_exception' , `__cxa_throw' , `operator delete(void*)'
   
    *   included '-lstdc++' library in LIBS variable <configure.ac>
   
71.warning: aclocal.m4:16: this file was generated for autoconf 2.65.
   You have another version of autoconf.  It may work, but is not guaranteed to.
   If you have problems, you may need to regenerate the build system entirely.
   
   * install autoconf-2.65
   
       $ wget http://ftp.gnu.org/gnu/autoconf/autoconf-2.65.tar.gz
       $ tar xvfvz autoconf-2.65.tar.gz
       $ cd autoconf-2.65
       $ ./configure
       $ make
       $ sudo make install
    
72.PropDbGame.c
    Inspection Warning : 
    
        Called object is not a function (at line 357)
    
            *   removed macro ARGS()
                
                'prop_game_set_game_scalar_sexp_fsm' , 'prop_game_set_game_bool_sexp_fsm'
                'prop_game_set_game_bdd_fsm' , 'prop_game_set_game_be_fsm'
                
        Can't resolve type 'bool'
        
            *   included '#include <stdbool.h>' library
            
        Instantiating an unknown structure without a reference at line
        
            *   added bracket for single value enum types
            
                typedef enum { Game_Who_TAG } Game_Who;
                typedef enum { Game_UnrealizableCore_Algorithm_TAG } Game_UnrealizableCore_Algorithm;
                typedef enum { Game_UnrealizableCore_CoreType_TAG } Game_UnrealizableCore_CoreType;
                typedef enum { Game_SF07_StrategyPrintingMode_TAG } Game_SF07_StrategyPrintingMode

73.Runtime Errors

    1.smgameMain.c : Segmentation fault.
    
    *    in 'BannerPrint' replaced 'nusmv_stdout' with 'stdout' and 'nusmv_stderr' with 'stderr'

    2.smgameCmd.c in 'Smgame_AddCmd' :  Assertion `res' failed.
    
    *   replace NuSMV reset with NuGaT reset
    
    3.unknown command 'read_model'
    
    *   included this code in main() of NuGaT after 'FP_V_E iq_fns[][2] = {{NuGaTAddons_Init, NuGaTAddons_Quit}' declaration
    
            #if NUSMV_HAVE_INTERACTIVE_SHELL
                /* these are for the interactive shell */
                {CInit_init_cmd, CInit_quit_cmd},
                {Compass_init_cmd, Compass_Cmd_quit},
            #endif
    
74.CMake Partial Migration for Debug Purpose

    1.undefined reference to `MMalloc' ...
    
    *   added in CMakeLists.txt
    
            target_link_libraries(NuGaT
                    ${NUSMV_DIR}/build/build-cudd/lib/libst.a
                    ${NUSMV_DIR}/build/build-cudd/lib/libcudd.a
                    ...)
                    
    2.libxml2.a : 
    
        in `xmlFreeZMemBuff': undefined reference to `deflateEnd' ...
    
        *   added '/usr/lib/x86_64-linux-gnu/libz.a' in target_link_libraries() for 'CMakeLists.txt'
    
        in `xz_decomp' : undefined reference to `lzma_code'
    
        *   installed apt-get install liblzma-dev
        
75.Runtime Error

    1.NuGaT: /home/lorenzo/Desktop/NuSMV-2.6.0/NuSMV/code/nusmv/core/cinit/NuSMVEnv.c:174: NuSMVEnv_get_value: Assertion `(void*)((void *)0) != res' failed.

        grammar.y.2.55
        
        *   replaced  
                'NuSMVEnv_get_value(__nusmv_parser_env__, ENV_STRING_MGR)' with '__nusmv_parser_env__' for Game_Mode_Enter() and Game_Mode_Exit() functions
                'OptsHandler_create()' with 'GET_OPTS' macro
    
    2.PropDbGame.c:531 in prop_db_game_init for  NuSMVEnv_set_value ()
    
        *   see 53.2 revision
        
    3.gamePkg.c:322 : game_pkg_switch_to_prop_db_game (env=0x907ce0)
    
    *   replaced 
            'dbg = PROP_DB_GAME(NuSMVEnv_get_value(env, ENV_PROP_DB));' with 'dbg = PROP_DB_GAME(NuSMVEnv_remove_value(env, ENV_PROP_DB));'
            'db = PROP_DB_GAME(NuSMVEnv_get_value(env, ENV_PROP_DB));' with 'db = PROP_DB_GAME(NuSMVEnv_remove_value(env, ENV_PROP_DB));'
       
    4.gameFlatten.c:227  fprintf (__fmt=0x6892d8 "*** WARNING: Game addon does not support properties COI size sorting.  ***\n", __stream=<optimized out>)
    
    *   replaced 'nusmv_stderr' with 'stderr' in Game_CommandFlattenHierarchy()

    5.PropDbGame.c:330: PropDbGame_master_get_game_scalar_sexp_fsm: Assertion `PropGame_type_is_game_or_notype(Prop_get_type(((Prop_ptr) prop)))'
    
    *   replaced 'PropPkg_get_prop_database' with NuSMVEnv_get_value(env, ENV_PROP_DB)
    
    6.gameGeneral.c:185 : iofwrite.c: No such file or directory.
    
    *   replaced all 'nusmv_stdout' with 'stdout' and all 'nusmv_stderr' with 'stderr'  
    
    7.gameGeneral.c:133: Game_BeforeCheckingSpec: Assertion `((GameBddFsm_ptr) fsm) != ((GameBddFsm_ptr) ((void *)0))' failed.
    
    *   see 53.2 revision   
    
    8.dd.c Program received signal SIGSEGV, Segmentation fault. 0x00000000006a3faa in Cudd_RecursiveDeref () for Compile_quit(env) -> BddFsm_destroy(bdd_fsm)
    
    *   removed all master property variables from environment
    
                NuSMVEnv_remove_value(env, ENV_SEXP_FSM); NuSMVEnv_remove_value(env, ENV_BOOL_FSM);
                NuSMVEnv_remove_value(env, ENV_BDD_FSM); NuSMVEnv_remove_value(env, ENV_BE_FSM);

.

================================================================================
EOF
================================================================================

FUTURE TODO

    - MIGRATION FROM fprintf to [ StreamMgr_print_error(streams , OStream_printf , ... ]
    - REMOVE ALL COMMENTED LINES
    
----
    - RECONVERT LOG IN A SMART WAY (like a list, remove all rendundant words)