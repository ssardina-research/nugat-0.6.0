cmake_minimum_required(VERSION 3.2)

project(NuGaT)
set(PROJECT_VERSION "0.6.0")


set(NUGAT_SOURCE_DIR .)

set(NUSMV_SOURCE_DIR "/home/lorenzo/Documents/software/ClionProjects/NuSMV-2.6.0/NuSMV"
    CACHE PATH "Source directory of NuSMV")

set(NUSMV_BUILD_DIR "/opt/NuSMV-2.6.0/"
    CACHE PATH "Build directory of NuSMV")


include_directories(${NUSMV_BUILD_DIR}/include)
include_directories(${NUSMV_BUILD_DIR}/include/code)
include_directories(${NUSMV_BUILD_DIR}/include/code/nusmv/core)
include_directories(${NUSMV_BUILD_DIR}/include/code/nusmv/shell)

## Somehow some .h files are not copied to the install directory and remain only in the source tree of NuSMV
## so we need to include those source dirs. shouldn't they be copied to the install dir too?
#
# for nusmv/core/parser/grammar.y
include_directories(${NUSMV_SOURCE_DIR}/build/code/)
# for nusmv/core/compile/type_checking/checkers/checkersInt.h
include_directories("${NUSMV_SOURCE_DIR}/code")
# for compile/type_checking/checkers/CheckerBase_private.h
include_directories("${NUSMV_SOURCE_DIR}/code/nusmv/core")


#include_directories("${NUSMV_SOURCE_DIR}/build/build-MiniSat/minisat-37dc6c67e2af26379d88ce349eb9c4c6160e8543")

include_directories(${NUGAT_SOURCE_DIR})
include_directories("${NUGAT_SOURCE_DIR}/src")
include_directories("${NUGAT_SOURCE_DIR}/src/parser")


set(SOURCE_FILES
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
        src/parser/Makefile.am
        src/parser/Makefile.in
        src/smgame/smgameCmd.c
        src/smgame/smgameDummyMac.c
        src/smgame/smgameInit.c
        src/smgame/smgameInt.h
        src/smgame/smgameMain.c
        src/smgame/smgameMisc.c
        src/smgame/smgameVers.c
        )


file(GLOB_RECURSE NUSMV_SRC
        "${NUGAT_SOURCE_DIR}/src/parser/*.c"
        "${NUSMV_DIR}/code/*.c"
        )

list(REMOVE_ITEM NUSMV_SRC
        "${NUSMV_DIR}/code/nusmv/core/dag/dagEn.c"
        "${NUSMV_DIR}/code/nusmv/core/sat/solvers/SatZchaff.c"
        "${NUSMV_DIR}/code/nusmv/core/trace/loaders/TraceXmlLoader.c"
        "${NUSMV_DIR}/code/nusmv/core/utils/utils_msvc.c"
        "${NUSMV_DIR}/code/nusmv/core/utils/BigWordNumberMgr.c"
        "${NUSMV_DIR}/code/nusmv/core/utils/BigWordNumberInt.c"
        "${NUSMV_DIR}/code/nusmv/core/utils/bignumbers/bignumbers.c"
        ${NUSMV_DIR}/code/nusmv/core/utils/bignumbers/numbers.c
        "${NUSMV_DIR}/code/nusmv/core/utils/BigWordNumber.c"
        "${NUSMV_DIR}/code/nusmv/core/parser/psl/psl.c"
        "${NUSMV_DIR}/code/wtest/src/main.c"
        "${NUSMV_DIR}/code/nusmv/core/bmc/bmcPkg.c"
        "${NUSMV_DIR}/code/nusmv/core/compile/compileBEval.c"
        "${NUSMV_DIR}/code/nusmv/core/trace/pkg_trace.c"

        "${NUSMV_DIR}/code/nusmv/ltl2smvMain.c"
        "${NUSMV_DIR}/code/nusmv/main.c"
        "${NUSMV_DIR}/build/build-MiniSat/minisat-37dc6c67e2af26379d88ce349eb9c4c6160e8543/CMakeFiles/3.2.2/CompilerIdC/CMakeCCompilerId.c"


        )


add_executable(NuGaT ${SOURCE_FILES} ${NUSMV_SRC} )

# ALL THIS DOES NOT WORK, WE NEED TO LINK AGAINST MANY FILES .a
#FIND_LIBRARY(NUSMV_LIBRARY NAMES nusmv /opt/NuSMV-2.6.0/lib/libnusmvshell.a)
#find_library(NUSMV_LIBRARY NAMES nusmvshell.a nusmvaddonscore.a nusmvcore nusmvgrammar  nusmvrbc MiniSat
#        HITNS /opt/NuSMV-2.6.0/lib/ NO_DEFAULT_PATH)
##find_library(NUSMV_LIBRARY NAMES nusmvshell.a nusmvaddonscore.a
#        PATHS ${NUSMV_BUILD_DIR}/lib/ NO_DEFAULT_PATH)
#find_library(NUSMV_LIBRARY NAMES nusmvaddonscore.a
#        PATHS /opt/NuSMV-2.6.0/lib/ NO_DEFAULT_PATH)



# Link to NUSMV libraries
foreach(X nusmvshell nusmvaddonscore nusmvcore nusmvgrammar nusmvrbc MiniSat)
        find_library(NUSMV_${X}_LIBRARY NAMES ${X}
            PATHS ${NUSMV_BUILD_DIR}/lib/ NO_DEFAULT_PATH)
        target_link_libraries(NuGaT ${NUSMV_${X}_LIBRARY})
endforeach()

# Link to CUDD libraries
foreach(X libst.a libcudd.a libepd.a libmtr.a libutil.a)
    find_library(CUDD_${X}_LIBRARY NAMES ${X}
            PATHS ${NUSMV_DIR}/build/build-cudd/lib/ NO_DEFAULT_PATH)
    target_link_libraries(NuGaT ${CUDD_${X}_LIBRARY})
endforeach()

# Link to system libraries (these should be found automatically in standard dirs)
target_link_libraries(NuGaT
            libstdc++.a
            libxml2.a
            libreadline.a
            libtermcap.a
            libexpat.a
            libz.a
            liblzma.a
            libm.a
            )
#

add_definitions(-DHAVE_EXTERN_ARGS_MACROS)
add_definitions(-DHAVE_CONFIG_H)