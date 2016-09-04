add_subdirectory(game)

set(SRCS
  addonsPkg.c
  )

nugat_add_pkg_lib(${SRCS})

nugat_add_pkg_headers(addons.h)
