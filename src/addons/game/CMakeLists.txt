set(SRCS
  	walkers/CheckerGame.c
	walkers/PrinterGame.c
	walkers/PrinterSexpGame.c

	fsm/GameBddFsm.c
	fsm/GameBeFsm.c
	fsm/GameSexpFsm.c

  	TypeCheckerGame.c
	PropGame.c
	PropDbGame.c
	gameXmlReader.c
	gameWriteModel.c
	gameVarEncoding.c
	gameUnrealCore.c
	GameStrategy.c
	gameReqToGame.c
	GamePlayer.c
	gamePkg.c
	gameOpt.c
	GameHierarchy.c
	gameGeneral.c
	gameFlatten.c
	gameCmd.c
	gameCheckReachAvoidSpec.c
	gameCheckLTLSF07_gba_wring.c
	gameCheckLTLSF07_gba.c
	gameCheckLTLSF07.c
	gameCheckGenReactivityBuchiSpec.c
	gameBuildModel.c
  )

nugat_add_pkg_lib(${SRCS})

set(HDRS

	walkers/CheckerGame.h
	walkers/CheckerGame_private.h
	walkers/PrinterGame.h
	walkers/PrinterGame_private.h
	walkers/PrinterSexpGame.h
	walkers/PrinterSexpGame_private.h

	fsm/GameBddFsm.h
	fsm/GameBeFsm.h
	fsm/GameSexpFsm.h

	parser/game_symbols.h

	TypeCheckerGame.h
	PropGame_private.h
	PropGame.h
	PropDbGame_private.h
	PropDbGame.h
	GameStrategy.h
	GamePlayer.h
	gameInt.h
	GameHierarchy.h
	gameCmd.h
	gameCheckLTLSF07_gba_wring.h
	gameCheckLTLSF07_gba.h
	game.h)

nugat_add_pkg_headers(${HDRS})
