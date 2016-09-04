if (MSVC)
    add_definitions(-DYY_NO_UNISTD_H)
endif()

nugat_combine_scanner("${CMAKE_CURRENT_BINARY_DIR}/input.l"
#  input.l.1.25
#  input.l.1.50

  input.l.1.55

#  input.l.2.25
#  input.l.2.50
#
#  input.l.2.55
#
#  input.l.2.51
#  input.l.2.75
#  input.l.3.50
  )

nugat_combine_grammar(begin "${CMAKE_CURRENT_BINARY_DIR}/grammar.y"
#  grammar.y.1.25
#  grammar.y.1.50

  grammar.y.1.55

#  grammar.y.2.50
#  grammar.y.2.51
#
#  grammar.y.2.55
#
#  grammar.y.3.50
  )

flex_target(nugat_core_lexer
            "${CMAKE_CURRENT_BINARY_DIR}/input.l"
            "${CMAKE_CURRENT_BINARY_DIR}/input.c"
            COMPILE_FLAGS "-Pnugat_yy")

bison_target(nugat_core_parser
             "${CMAKE_CURRENT_BINARY_DIR}/grammar.y"
             "${CMAKE_CURRENT_BINARY_DIR}/grammar.c"
             COMPILE_FLAGS "-d -p nugat_yy")

set(GRAMMAR_SRCS
    "${CMAKE_CURRENT_BINARY_DIR}/input.c"
    "${CMAKE_CURRENT_BINARY_DIR}/grammar.c"
    )
nugat_get_pkg_name(_curpkg)
nugat_add_pkg(${_curpkg}_grammar grammar ${GRAMMAR_SRCS}) #  ${GRAMMAR_SRCS} files not found


