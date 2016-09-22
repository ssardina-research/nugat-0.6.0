cmake_minimum_required(VERSION 2.8.8)
cmake_policy(VERSION 2.8)

project(NuGaT)
set(PROJECT_VERSION "0.6.0")

set(CMAKE_MODULE_PATH ${PROJECT_SOURCE_DIR}/cmake)
include(NuGATUtils)
include(FindICU)
set(NUGAT_SOURCE_DIR .)

#------------------------------------------------------------------------------
# User has to set up environment variables NUSMV_SOURCE_DIR and NUSMV_BUILD_DIR
#------------------------------------------------------------------------------

#set(NUSMV_SOURCE_DIR "/home/ssardina/src/NuSMV/NuSMV-2.6.0/NuSMV"
#    CACHE PATH "Source directory of NuSMV")
#set(NUSMV_BUILD_DIR "/opt/NuSMV-2.6.0/"
#    CACHE PATH "Build directory of NuSMV")

if(NOT EXISTS "$ENV{NUSMV_SOURCE_DIR}")
    message(FATAL_ERROR "Could not find NUSMV_SOURCE_DIR environment variable")
else()
    set(NUSMV_SOURCE_DIR $ENV{NUSMV_SOURCE_DIR}
           CACHE PATH "Source directory of NuSMV")
endif(NOT EXISTS "$ENV{NUSMV_SOURCE_DIR}")

if(NOT EXISTS "$ENV{NUSMV_BUILD_DIR}")
    message(FATAL_ERROR "Could not find NUSMV_BUILD_DIR environment variable")
else()
    set(NUSMV_BUILD_DIR $ENV{NUSMV_BUILD_DIR}
            CACHE PATH "Build directory of NuSMV")
endif(NOT EXISTS "$ENV{NUSMV_BUILD_DIR}")


#-------------------
# GENERATE config.h
#-------------------
nugat_set_config_h_prefix("")

# some (for now?) hardcoded config values
nugat_set_config_h_01(CLOSEDIR_VOID 1)

nugat_set_config_h_str(EXEEXT "")

nugat_set_config_h_01(HAVE_CPP 1)
nugat_set_config_h_01(HAVE_DIRENT_H 1)
nugat_set_config_h_01(HAVE_DLFCN_H 1)
#nugat_set_config_h_01(HAVE_DOPRNT 1)
nugat_set_config_h_01(HAVE_ERRNO_H 1)
nugat_set_config_h_01(HAVE_EXTERN_ARGS_MACROS 1)
nugat_set_config_h_01(HAVE_FLOAT_H 1)
#nugat_set_config_h_01(HAVE_FLOOR 1)
nugat_set_config_h_01(HAVE_GAME 1)
#nugat_set_config_h_01(HAVE_GETENV 1)
#nugat_set_config_h_01(HAVE_GETPID 1)
nugat_set_config_h_01(HAVE_INTTYPES_H 1)
#nugat_set_config_h_01(HAVE_ISATTY 1)
nugat_set_config_h_01(HAVE_LIBEXPAT 1)
nugat_set_config_h_01(HAVE_LIBM 1)
nugat_set_config_h_01(HAVE_LIBREADLINE 1)
nugat_set_config_h_01(HAVE_LIMITS_H 1)
nugat_set_config_h_01(HAVE_MALLOC_H 1)
#nugat_set_config_h_01(HAVE_MEMMOVE 1)
nugat_set_config_h_01(HAVE_MEMORY_H 1)
#nugat_set_config_h_01(HAVE_MEMSET 1)
#nugat_set_config_h_01(HAVE_MKSTEMP 1)
#nugat_set_config_h_01(HAVE_MKTEMP 1)
#nugat_set_config_h_01(HAVE_NDIR_H 1)
#nugat_set_config_h_01(HAVE_POPEN 1)
#nugat_set_config_h_01(HAVE_POW 1)
#nugat_set_config_h_01(HAVE_RANDOM 1)
nugat_set_config_h_01(HAVE_REALLOC 0)
nugat_set_config_h_01(HAVE_REGEX_H 1)
nugat_set_config_h_01(HAVE_SAT_SOLVER 0)
#nugat_set_config_h_01(HAVE_SETVBUF 0)
nugat_set_config_h_01(HAVE_SIGNAL_H 1)
nugat_set_config_h_01(HAVE_SOLVER_MINISAT 1)
nugat_set_config_h_01(HAVE_SOLVER_ZCHAFF 0)
#nugat_set_config_h_01(HAVE_SRANDOM 0)
nugat_set_config_h_01(HAVE_STAT_EMPTY_STRING_BUG 1)
nugat_set_config_h_01(HAVE_STDBOOL_H 1)
nugat_set_config_h_01(HAVE_STDDEF_H 1)
nugat_set_config_h_01(HAVE_STDINT_H 1)
nugat_set_config_h_01(HAVE_STDLIB_H 1)
#nugat_set_config_h_01(HAVE_STRCASECMP 1)
#nugat_set_config_h_01(HAVE_STRCHR 1)
nugat_set_config_h_01(HAVE_STRINGS_H 1)
nugat_set_config_h_01(HAVE_STRING_H 1)
#nugat_set_config_h_01(HAVE_STRRCHR 1)
#nugat_set_config_h_01(HAVE_STRSTR 1)
#nugat_set_config_h_01(HAVE_STRTOL_ 1)
#nugat_set_config_h_01(HAVE_SYSTEM 1)
#nugat_set_config_h_01(HAVE_SYS_DIR_H 1)
nugat_set_config_h_01(HAVE_SYS_IOCTL_H 1)
#nugat_set_config_h_01(HAVE_SYS_MALLOC_H 1)
#nugat_set_config_h_01(HAVE_SYS_NDIR_H 1)
nugat_set_config_h_01(HAVE_SYS_PARAM_H 1)
nugat_set_config_h_01(HAVE_SYS_RESOURCE_H 1)
nugat_set_config_h_01(HAVE_SYS_SIGNAL_H 1)
nugat_set_config_h_01(HAVE_SYS_STAT_H 1)
nugat_set_config_h_01(HAVE_SYS_TIME_H 1)
nugat_set_config_h_01(HAVE_SYS_TYPES_H 1)
#nugat_set_config_h_01(HAVE_TMPNAM 1)
nugat_set_config_h_01(HAVE_UNISTD_H 1)
#nugat_set_config_h_01(HAVE_VPRINTF 1)
nugat_set_config_h_01(HAVE__BOOL 1)

nugat_set_config_h_str(LINKED_ADDONS "game ")
#nugat_set_config_h_01(LSTAT_FOLLOWS_SLASHED_SYMLINK 1)
nugat_set_config_h_str(LT_OBJDIR ".libs/")
#nugat_set_config_h_01(NO_MINUS_C_MINUS_O 1)

nugat_set_config_h_str(LIBRARY_NAME ${CMAKE_PROJECT_NAME})
nugat_set_config_h_str(LIBRARY_VERSION ${PROJECT_VERSION})
nugat_get_current_time(_now)
nugat_set_config_h_str(LIBRARY_BUILD_DATE "${_now}")
nugat_set_config_h_str(LIBRARY_WEBSITE "http://nusmv.fbk.eu")
nugat_set_config_h_str(LIBRARY_EMAIL "nugat@list.fbk.eu")
nugat_set_config_h_str(LIBRARY_BUGREPORT "Please report bugs to <nusmv-users@fbk.eu>")

nugat_set_config_h_str(PACKAGE_BUILD_DATE "${_now}")
nugat_set_config_h_str(PACKAGE_BUGREPORT ${LIBRARY_BUGREPORT})
nugat_set_config_h_str(PACKAGE_NAME ${LIBRARY_NAME})
nugat_set_config_h_str(PACKAGE_TARNAME "nugat")
nugat_set_config_h_str(PACKAGE_URL "")
nugat_set_config_h_str(PACKAGE_VERSION ${LIBRARY_VERSION})
nugat_set_config_h_str(PACKAGE_STRING "${PACKAGE_NAME} ${PACKAGE_VERSION}")

nugat_set_config_h_str(PROG_CPP gcc -E -x c)
nugat_set_config_h_str(RETSIGTYPE void)
nugat_set_config_h_str(SIZEOF_INT 4)
nugat_set_config_h_str(SIZEOF_LONG 8)
nugat_set_config_h_str(SIZEOF_LONG_LONG 8)
nugat_set_config_h_str(SIZEOF_VOID_P 8)
nugat_set_config_h_str(VERSION "0.6.0")
nugat_set_config_h_01(YYTEXT_POINTER 1)

# not commented originally
#nugat_add_config_h_val(realloc rpl_realloc)

nugat_write_config_h(config.h)

add_definitions(-DHAVE_CONFIG_H)
#-------------------
# END : GENERATE config.h
#-------------------

# ------------------
# INCLUDE DIRS
# ------------------

# NuSMV
include_directories("${NUSMV_BUILD_DIR}/include")
include_directories("${NUSMV_BUILD_DIR}/include/code")
include_directories("${NUSMV_BUILD_DIR}/include/code/nusmv/core")
include_directories("${NUSMV_BUILD_DIR}/include/code/nusmv/shell")

## Somehow some .h files are not copied to the install directory and remain only in the source tree of NuSMV
## so we need to include those source dirs. shouldn't they be copied to the install dir too?
include_directories(${NUSMV_SOURCE_DIR}/build/code/) # for nusmv/core/parser/grammar.y
include_directories(${NUSMV_SOURCE_DIR}/code) # for nusmv/core/compile/type_checking/checkers/checkersInt.h
include_directories(${NUSMV_SOURCE_DIR}/code/nusmv/core) # for compile/type_checking/checkers/CheckerBase_private.h
#include_directories("${NUSMV_SOURCE_DIR}/build/build-MiniSat/minisat-37dc6c67e2af26379d88ce349eb9c4c6160e8543")

# NuGAT
include_directories(${NUGAT_SOURCE_DIR})
include_directories(${NUGAT_SOURCE_DIR}/build)
include_directories(${NUGAT_SOURCE_DIR}/src)
include_directories(${NUGAT_SOURCE_DIR}/src/parser)

#-------------------
# END : INCLUDE DIRS
#-------------------

# ------------------
# PARSER
# ------------------
file(MAKE_DIRECTORY build/nusmv/core/parser)

nugat_combine_scanner("${CMAKE_CURRENT_BINARY_DIR}/input.l"

        #${NUSMV_SOURCE_DIR}/code/nusmv/core/parser/input.l.1.25
        ${NUSMV_SOURCE_DIR}/code/nusmv/core/parser/input.l.1.50

        ${NUSMV_SOURCE_DIR}/code/nusmv/core/parser/input.l.2.25
        ${NUSMV_SOURCE_DIR}/code/nusmv/core/parser/input.l.2.50
        src/parser/input.l.2.55
        #${NUSMV_SOURCE_DIR}/code/nusmv/core/parser/input.l.2.51
        ${NUSMV_SOURCE_DIR}/code/nusmv/core/parser/input.l.2.75

        ${NUSMV_SOURCE_DIR}/code/nusmv/core/parser/input.l.3.50
        )

nugat_combine_grammar(game_begin "${CMAKE_CURRENT_BINARY_DIR}/grammar.y"

        #${NUSMV_SOURCE_DIR}/code/nusmv/core/parser/grammar.y.1.25
        ${NUSMV_SOURCE_DIR}/code/nusmv/core/parser/grammar.y.1.50
        src/parser/grammar.y.1.55

        ${NUSMV_SOURCE_DIR}/code/nusmv/core/parser/grammar.y.2.50
        #${NUSMV_SOURCE_DIR}/code/nusmv/core/parser/grammar.y.2.51
        src/parser/grammar.y.2.55

        ${NUSMV_SOURCE_DIR}/code/nusmv/core/parser/grammar.y.3.50
        )

flex_target(nugat_core_lexer
        "${CMAKE_CURRENT_BINARY_DIR}/input.l"
        "${CMAKE_CURRENT_BINARY_DIR}/input.c"
        COMPILE_FLAGS "-Pnusmv_yy") # -l

bison_target(nugat_core_parser
        "${CMAKE_CURRENT_BINARY_DIR}/grammar.y"
        "${CMAKE_CURRENT_BINARY_DIR}/nusmv/core/parser/grammar.c"
        COMPILE_FLAGS "-d -p nusmv_yy")

set(GRAMMAR_SRCS
        "${CMAKE_CURRENT_BINARY_DIR}/input.c"
        "${CMAKE_CURRENT_BINARY_DIR}/nusmv/core/parser/grammar.c"
        )
nugat_get_pkg_name(_curpkg)
nugat_add_pkg(${_curpkg}_grammar grammar ${GRAMMAR_SRCS})

# ------------------
# END : PARSER
# ------------------

# ------------------
#  SOURCE FILES
# ------------------
set(SOURCE_FILES

        build/config.h

        build/nusmv/core/parser/grammar.c
        build/input.c

        src/addons/game/fsm/GameBddFsm.c
        src/addons/game/fsm/GameBddFsm.h
        src/addons/game/fsm/GameBeFsm.c
        src/addons/game/fsm/GameBeFsm.h
        src/addons/game/fsm/GameSexpFsm.c
        src/addons/game/fsm/GameSexpFsm.h

        src/addons/game/parser/game_symbols.h

        src/addons/game/walkers/CheckerGame.c
        src/addons/game/walkers/CheckerGame.h
        src/addons/game/walkers/CheckerGame_private.h
        src/addons/game/walkers/PrinterGame.c
        src/addons/game/walkers/PrinterGame.h
        src/addons/game/walkers/PrinterGame_private.h
        src/addons/game/walkers/PrinterSexpGame.c
        src/addons/game/walkers/PrinterSexpGame.h
        src/addons/game/walkers/PrinterSexpGame_private.h

        src/addons/game/game.h
        src/addons/game/gameBuildModel.c
        src/addons/game/gameCheckGenReactivityBuchiSpec.c
        src/addons/game/gameCheckLTLSF07.c
        src/addons/game/gameCheckLTLSF07_gba.c
        src/addons/game/gameCheckLTLSF07_gba.h
        src/addons/game/gameCheckLTLSF07_gba_wring.c
        src/addons/game/gameCheckLTLSF07_gba_wring.h
        src/addons/game/gameCheckReachAvoidSpec.c
        src/addons/game/gameCmd.c
        src/addons/game/gameCmd.h
        src/addons/game/gameFlatten.c
        src/addons/game/gameGeneral.c
        src/addons/game/GameHierarchy.c
        src/addons/game/GameHierarchy.h
        src/addons/game/gameInt.h
        src/addons/game/gameOpt.c
        src/addons/game/gamePkg.c
        src/addons/game/GamePlayer.c
        src/addons/game/GamePlayer.h
        src/addons/game/gameReqToGame.c
        src/addons/game/GameStrategy.c
        src/addons/game/GameStrategy.h
        src/addons/game/gameUnrealCore.c
        src/addons/game/gameVarEncoding.c
        src/addons/game/gameWriteModel.c
        src/addons/game/gameXmlReader.c
        src/addons/game/PropDbGame.c
        src/addons/game/PropDbGame.h
        src/addons/game/PropDbGame_private.h
        src/addons/game/PropGame.c
        src/addons/game/PropGame.h
        src/addons/game/PropGame_private.h
        src/addons/game/TypeCheckerGame.c
        src/addons/game/TypeCheckerGame.h

        src/addons/addons.h
        src/addons/addonsPkg.c

        src/smgame/printStrategy.h
        src/smgame/smgameCmd.c
        src/smgame/smgameDummyMac.c
        src/smgame/smgameInit.c
        src/smgame/smgameInt.h
        src/smgame/smgameMain.c
        src/smgame/smgameMisc.c
        src/smgame/smgameVers.c
        )

# ------------------
# END : SOURCE FILES
# ------------------

#file(GLOB_RECURSE NUSMV_SRC
#        "${NUSMV_SOURCE_DIR}/code/*.c"
#        )
#
#list(REMOVE_ITEM NUSMV_SRC
#
#        "${NUSMV_SOURCE_DIR}/code/nusmv/core/dag/dagEn.c"
#        "${NUSMV_SOURCE_DIR}/code/nusmv/core/sat/solvers/SatZchaff.c"
#        "${NUSMV_SOURCE_DIR}/code/nusmv/core/trace/loaders/TraceXmlLoader.c"
#        "${NUSMV_SOURCE_DIR}/code/nusmv/core/utils/utils_msvc.c"
#        "${NUSMV_SOURCE_DIR}/code/nusmv/core/utils/BigWordNumberMgr.c"
#        "${NUSMV_SOURCE_DIR}/code/nusmv/core/utils/BigWordNumberInt.c"
#        "${NUSMV_SOURCE_DIR}/code/nusmv/core/utils/bignumbers/bignumbers.c"
#        "${NUSMV_SOURCE_DIR}/code/nusmv/core/utils/bignumbers/numbers.c"
#        "${NUSMV_SOURCE_DIR}/code/nusmv/core/utils/BigWordNumber.c"
#        "${NUSMV_SOURCE_DIR}/code/nusmv/core/parser/psl/psl.c"
#        "${NUSMV_SOURCE_DIR}/code/wtest/src/main.c"
#        "${NUSMV_SOURCE_DIR}/code/nusmv/core/bmc/bmcPkg.c"
#        "${NUSMV_SOURCE_DIR}/code/nusmv/core/compile/compileBEval.c"
#        "${NUSMV_SOURCE_DIR}/code/nusmv/core/trace/pkg_trace.c"
#
#        "${NUSMV_SOURCE_DIR}/code/nusmv/ltl2smvMain.c"
#        "${NUSMV_SOURCE_DIR}/code/nusmv/main.c"
#        "${NUSMV_SOURCE_DIR}/build/build-MiniSat/minisat-37dc6c67e2af26379d88ce349eb9c4c6160e8543/CMakeFiles/3.2.2/CompilerIdC/CMakeCCompilerId.c"
#        )


# ------------------
# LINK TO LIBS
# ------------------

add_executable(NuGaT ${SOURCE_FILES}) # ${NUSMV_SRC}

# Link to NUSMV libraries
foreach(X nusmvshell nusmvaddonscore nusmvcore nusmvgrammar nusmvrbc MiniSat)
        find_library(NUSMV_${X}_LIBRARY NAMES ${X}
            PATHS ${NUSMV_BUILD_DIR}/lib/ NO_DEFAULT_PATH)
        target_link_libraries(NuGaT ${NUSMV_${X}_LIBRARY})
endforeach()

# Link to CUDD libraries
foreach(X libst.a libcudd.a libepd.a libmtr.a libutil.a)
    find_library(CUDD_${X}_LIBRARY NAMES ${X}
            PATHS ${NUSMV_SOURCE_DIR}/build/build-cudd/lib/ NO_DEFAULT_PATH)
    target_link_libraries(NuGaT ${CUDD_${X}_LIBRARY})
endforeach()

# Link to system libraries (these should be found automatically in standard dirs)
target_link_libraries(NuGaT libstdc++.a libxml2.a libreadline.a libtermcap.a libexpat.a libz.a liblzma.a  libicuuc.a libicudata.a)
target_link_libraries(NuGaT m dl)
# ------------------
# END : LINK TO LIBS
# ------------------