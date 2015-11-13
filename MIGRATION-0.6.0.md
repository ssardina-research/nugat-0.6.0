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

4.Error: statement EXTERN is missing 
    
    *   added this 2 lines in config.h.in
    
            /* Define to 1 if the system has EXTERN and ARGS */
            #define HAVE_EXTERN_ARGS_MACROS 1

5.Warning: ggrammar.y:1076:38: warning: passing argument 1 of ‘opt_game_game’ makes pointer from integer without a cast
                        if (!opt_game_game(OptsHandler_get_instance())) {...

    *   This is because NuSMV has renamed  OptsHandler_get_instance with OptsHandler_create
    *   Rename all calls to OptsHandler_get_instance with OptsHandler_create in NuGat code.

6.Warning: macro ...  
    .1 "new_node" requires 4 arguments, but only 3 given -> added 'nodemgr' parameter
    .2 "cons" requires 3 arguments, but only 2 given -> added 'nodemgr' parameter
    .3 "new_lined_node" requires 5 arguments, but only 4 given -> added 'nodemgr' parameter
    .4 "find_node" requires ... -> added 'nodemgr' parameter
    .5 "print_node" requires ... -> added 'wffprint' parameter
    
    *   added this lines before the usage 
    
            const NuSMVEnv_ptr env = EnvObject_get_environment(ENV_OBJECT(self));
            const NodeMgr_ptr nodemgr = NODE_MGR(NuSMVEnv_get_value(env, ENV_NODE_MGR));
            const MasterPrinter_ptr wffprint = MASTER_PRINTER(NuSMVEnv_get_value(env, ENV_WFF_PRINTER));

7.Warning: grammar.y.: implicit declaration of function ‘yylex’,‘yyerror’ and ‘yyerror_lined’

     *   change in parser/Makefile(.am and .in)
        
            **  the flags
                AM_YFLAGS = -d -p nusmv_yy
                AM_LFLAGS = -l -Pnusmv_yy

    *   replace in grammar.y.2.55 'yyerror_lined' with 'nusmv_yyerror_lined'
        
8.Error: grammar.y : function 'find_string' not found

    *   'find_string(' has been replaced 
    
            by 'UStringMgr_find_string(strings,' with 'strings' declaration 'UStringMgr_ptr strings = USTRING_MGR(NuSMVEnv_get_value(env, ENV_STRING_MGR));'
            
            and in grammar.y.2.55 with 'UStringMgr_find_string(USTRING_MGR(NuSMVEnv_get_value(__nusmv_parser_env__, ENV_STRING_MGR)),'
            
        
9.Error : input.l: ‘nusmv_yytext’ undeclared (first use in this function) ------------- ^"#"" "[0-9]+.*\n       sscanf(nusmv_yytext,"# %d",&nusmv_yylineno); 
            
    *   added this variable after 'AM_LFLAGS' in the parser/Makefile(.am and .in)
        
            LEX_OUTPUT_ROOT = lex.nusmv_yy
       
10.Error: input.l : ‘yylval’ undeclared (first use in this function)

    *   replaced in input.2.55 the string 'yylval' with 'nusmv_yylval' and 'yylineno' with 'nusmv_yylineno'

11.Error: input.l : ‘TOK_GAME’ undeclared (first use in this function) 

    *   added a new file parser/input.l.1.55 with '#include "grammar.h"' 
    *   included this file (input.l.1.55) in parser/Makefile(.am and .in) after input.l.1.50
    *   added 'src/parser/input.l.1.55' in CMakeList.txt

12.Error: gameOpt.c : too few arguments to function ‘OptsHandler_register_option’

    *   added argument to Game_init_opt(NuSMVEnv_ptr const env) in gameInt.h and gameOpt.c 
    *   in gamePkg.c
            -added in head 'NuSMVEnv_ptr env = NuSMVEnv_create();' and update 'Game_init_opt();' with 'Game_init_opt(env);' in 'void Game_Init(void)'
            -append these 2 libraries
            
                    #include "nusmv/core/utils/StreamMgr.h"
                    #include "nusmv/core/cinit/NuSMVEnv.h"
                   
13.Error: GamePlayer.c : ‘USTRING_MGR’ undeclared (first use in this function)

    *   'USTRING_MGR' has been replaced by 'USTRING_MGR(NuSMVEnv_get_value(__nusmv_parser_env__, ENV_STRING_MGR))'
    *   added this line below the #include code
            
            extern NuSMVEnv_ptr __nusmv_parser_env__;
    
14.Warning: GameStrategy.c : passing argument 1 of ‘bdd_free’ from incompatible pointer type

    *   replaced 'DdManager*' with 'DDMgr_ptr' in all files

15.Warning: GameStrategy.c : implicit declaration of function ‘Enc_get_bdd_encoding’

    *   is replaced with: if 'fsm' variable is 
        -present 
        
                BddFsm_get_bdd_encoding(BDD_FSM(fsm))
                BddFsm_get_bdd_encoding(BDD_FSM(scalar_fsm)) 
                BddFsm_get_bdd_encoding(BDD_FSM(bool_fsm)) ('enc' and 'st' dropped below the 'bool_fsm' declaration)
                
        -not present
                
                BddFsm_get_bdd_encoding(BDD_FSM(GAME_BDD_FSM(NULL)));
                BddFsm_get_bdd_encoding(BDD_FSM(GAME_SEXP_FSM(NULL)));
                
16.Warning: GameStrategy.c: passing argument 1 of ‘print_node’ from incompatible pointer type
   
    *   replace print_node(...) with print_node(wffprint,...)
        replaced SymbType_print(...) with SymbType_print(... , wffprint , ...)
           
        changed this functions in GameStrategy.c and gameCheckLTLSF07.c
              
           -added this lines in head of GameStrategy_print_module() 
                   
                   env = EnvObject_get_environment(ENV_OBJECT(st));
                   const MasterPrinter_ptr wffprint = _PRINTER(NuSMVEnv_get_value(env, ENV_WFF_PRINTER));
   
   
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
                           

17.Warning: GameStrategy.c: passing argument 7 of ‘BddEnc_print_bdd_wff’ from incompatible pointer type

    *   replaced the parameter "out" with "OSTREAM(out)"

18.Warning: gameCmd.c:  initialization from incompatible pointer type {"read_rat_file",        CommandReadRatFile, 0, true},

    *   added the "NuSMVEnv_ptr env" parameter in functions declaration
        
            static int Command...(NuSMVEnv_ptr env,...)

19.Error: gameCmd.c:  ‘nusmv_stderr’ undeclared (first use in this function) 

    *   replaced 'nusmv_stdout' with 'stdout' and 'nusmv_stderr' with 'stderr'
    
20.Warning: gameCmd.c:  implicit declaration of function ‘nusmv_exit’ 

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

21.Error: gameCmd.c:  ‘CATCH’ undeclared (first use in this function)
                         
    *   replaced "CATCH" with "CATCH(errmgr)" and "FAIL" with "FAIL(errmgr)" and added this lines of declaration
    
            NuSMVEnv_ptr const env = EnvObject_get_environment(ENV_OBJECT(self->symb_table));  ( ONLY IF 'env' IS NOT DECLARED )
            ErrorMgr_ptr const errmgr = ERROR_MGR(NuSMVEnv_get_value(env, ENV_ERROR_MANAGER));
                        
22.Warning: gameCmd.c: implicit declaration of function ‘PropPkg_get_prop_database’

    *   replaced with variable "prop_db" and declaration
    
            PropDb_ptr prop_db  = PROP_DB(NuSMVEnv_get_value(env, ENV_PROP_DB));
            
23.Error: gameCmd.c: ‘USTRING_MGR’ undeclared (first use in this function)

    *   *   'USTRING_MGR' has been replaced by 'USTRING_MGR(NuSMVEnv_get_value(env, ENV_STRING_MGR))'
    
24.Warning: gameCmd.c:  passing argument 2 of ‘PropDb_print_list_header’ from incompatible pointer type

    *   added "OStream_ptr ostream_ptr_nusmv_output = OStream_create(nusmv_stdout);" before the 'PropDb_print_list_header()' function
    *   replaced for :
            'PropDb_print_list_header()' and 'PropDb_print_prop_at_index()' -> 'nusmv_output' with 'ostream_ptr_nusmv_output'
            
25.Error: gameCmd.c:  ‘dd_manager’ undeclared (first use in this function)

    *   added declaration "DDMgr_ptr dd_manager = (DDMgr_ptr )NuSMVEnv_get_value(env, ENV_DD_MGR);"
    
26.Warning: gamePkg.c: implicit declaration of function

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
    

================================================================================
EOF
================================================================================
