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
    
    *   added this 2 rows in <config.h>
    
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

    *   'find_string' has been replaced by 'UStringMgr_find_string(USTRING_MGR,' and in <grammar.y.2.55> with 'UStringMgr_find_string(USTRING_MGR(NULL),'
    
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

    *   added argument to Game_init_opt(NuSMVEnv_ptr const env)

================================================================================
EOF
================================================================================
