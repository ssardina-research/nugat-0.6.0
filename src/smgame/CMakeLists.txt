set(SRCS
  	smgameCmd.c
	smgameDummyMac.c
	smgameInit.c
	smgameMain.c
	smgameMisc.c
	smgameVers.c
  )

nugat_add_pkg_lib(${SRCS})

set(HDRS
	printStrategy.h
	smgameInt.h
	)

nugat_add_pkg_headers(${HDRS})
