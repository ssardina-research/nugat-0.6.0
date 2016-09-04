set(SUBDIRS
  parser
  addons
  smgame
  )

foreach(_d ${SUBDIRS})
    add_subdirectory(${_d})
endforeach()
