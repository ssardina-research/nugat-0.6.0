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

4.Error: statement EXTERN is missing [TODO alternative solution : include NuSMV-2.6.0/NuSMV/code/nusmv/core/utils/defs.h]
    
    *   added the statement of EXTERN in nugat-0.5.4/src/addons/game/fsm/GameSexpFsm.h 

5.Warning: ggrammar.y:1076:38: warning: passing argument 1 of ‘opt_game_game’ makes pointer from integer without a cast
                        if (!opt_game_game(OptsHandler_get_instance())) {...

    *   This is because NuSMV has renamed  OptsHandler_get_instance with OptsHandler_create
    *   Rename all calls to OptsHandler_get_instance with OptsHandler_create in NuGat code.

6.Warning: macro ... [TODO: understand how to use new parameter]
    .1 "new_node" requires 4 arguments, but only 3 given
    .2 "cons" requires 3 arguments, but only 2 given
    .3 "new_lined_node" requires 5 arguments, but only 4 given
    .4 {and others functions} 
    
    * added this 2 lines before the usage of 'nodemgr'

7. Error : input.l:127:8: ‘nusmv_yytext’ undeclared (first use in this function) ------------- ^"#"" "[0-9]+.*\n       sscanf(nusmv_yytext,"# %d",&nusmv_yylineno); 

    *   [ how input.c is created? ]

8.

9.

10. 

================================================================================
EOF
================================================================================
