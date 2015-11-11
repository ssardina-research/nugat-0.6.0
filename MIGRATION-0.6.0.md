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
    
    *   added this 2 lines in <config.h.in>
    
            /* Define to 1 if the system has EXTERN and ARGS */
            #define HAVE_EXTERN_ARGS_MACROS 1

5.Warning: ggrammar.y:1076:38: warning: passing argument 1 of ‘opt_game_game’ makes pointer from integer without a cast
                        if (!opt_game_game(OptsHandler_get_instance())) {...

    *   This is because NuSMV has renamed  OptsHandler_get_instance with OptsHandler_create
    *   Rename all calls to OptsHandler_get_instance with OptsHandler_create in NuGat code.

6.Warning: macro ... 
    .1 "new_node" requires 4 arguments, but only 3 given
    .2 "cons" requires 3 arguments, but only 2 given
    .3 "new_lined_node" requires 5 arguments, but only 4 given
    .4 {and others functions} 
    
    *   added this 2 lines before the usage of 'nodemgr'

7.Warning: grammar.y.: implicit declaration of function ‘yylex’,‘yyerror’ and ‘yyerror_lined’

    *   changed content in <src/config.status> -> S["YFLAGS"]="-d -p nusmv_yy"
    *   replace in <grammar.y.2.55> 'yyerror_lined' with 'nusmv_yyerror_lined'
        
8.Error: grammar.y : function 'find_string' not found

    *   'find_string' has been replaced by 'UStringMgr_find_string(USTRING_MGR,' and in <grammar.y.2.55> with 'UStringMgr_find_string(USTRING_MGR(NuSMVEnv_get_value(__nusmv_parser_env__, ENV_STRING_MGR)),'
    
9.Error : input.l: ‘nusmv_yytext’ undeclared (first use in this function) ------------- ^"#"" "[0-9]+.*\n       sscanf(nusmv_yytext,"# %d",&nusmv_yylineno); 

    *   change in <parser/Makefile(.am and .in)>
    
        **  the flags
            AM_YFLAGS = -d -p nusmv_yy
            AM_LFLAGS = -l -Pnusmv_yy
            
        **  added this variable after this 2 flags
            LEX_OUTPUT_ROOT = lex.nusmv_yy
       
10.Error: input.l : ‘yylval’ undeclared (first use in this function)

    *   replaced in <input.2.55> the string 'yylval' with 'nusmv_yylval' and 'yylineno' with 'nusmv_yylineno'

11.Error: input.l : ‘TOK_GAME’ undeclared (first use in this function) [ TODO : FIND ANOTHER SOLUTION? )]

    *   commented the file <input.l.2.55>   

12.Error: gameOpt.c : too few arguments to function ‘OptsHandler_register_option’

    *   added argument to Game_init_opt(NuSMVEnv_ptr const env) in <gameInt.h> and <gameOpt.c> 
    *   in <gamePkg.c>
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
   
           -replace print_node(...) with print_node(wffprint,...)
           -replaced SymbType_print(...) with SymbType_print(... , wffprint , ...)
           
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

    *   added declaration in "Variable Declaration" section
    
20.Warning: gameCmd.c:  implicit declaration of function ‘nusmv_exit’ 

    *   replaced all 'nusmv_exit' with 'ErrorMgr_nusmv_exit(errmgr,'
    *   added this lines in head where nusmv_exit is replaced
    
            const NuSMVEnv_ptr env = EnvObject_get_environment(ENV_OBJECT(...));
            const ErrorMgr_ptr errmgr = 
                    ERROR_MGR(NuSMVEnv_get_value(env, ENV_ERROR_MANAGER));
                    
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
            ErrorMgr_ptr const errmgr =
                        ERROR_MGR(NuSMVEnv_get_value(env, ENV_ERROR_MANAGER));

================================================================================
EOF
================================================================================
