#
# Custom macros used in the build scripts of NuGAT and related tools
#

# first, make sure the NUGAT_SOURCE_DIR var is always set
if(NOT NUGAT_SOURCE_DIR)
    set(NUGAT_SOURCE_DIR "${CMAKE_CURRENT_LIST_DIR}/..")
endif()

# fix weird behaviour of "ar" with object files with the same basename. See
# https://essvn.fbk.eu/bugs/view.php?id=4437
if(UNIX OR MINGW)
    set(_archive_create "\"${CMAKE_COMMAND}\" -E remove -f <TARGET>" "<CMAKE_AR> cq <TARGET> <LINK_FLAGS> <OBJECTS>")
    set(_archive_append "<CMAKE_AR> q <TARGET> <LINK_FLAGS> <OBJECTS>")

    set(CMAKE_C_ARCHIVE_CREATE ${_archive_create})
    set(CMAKE_CXX_ARCHIVE_CREATE ${_archive_create})
    set(CMAKE_C_ARCHIVE_APPEND ${_archive_append})
    set(CMAKE_CXX_ARCHIVE_APPEND ${_archive_append})

    if(CMAKE_COMPILER_IS_GNUCC)
        add_definitions(-fPIC)
    endif()
endif()

# inline
#macro(nugat_check_inline)
#  FOREACH(KEYWORD "inline" "__inline__" "__inline")
#    IF(NOT DEFINED C_INLINE)
#      TRY_COMPILE(C_HAS_${KEYWORD} "${PROJECT_BINARY_DIR}"
#        "${NUGAT_SOURCE_DIR}/cmake/test-inline.c"
#        COMPILE_DEFINITIONS "-Dinline=${KEYWORD}")
#
#      IF(C_HAS_${KEYWORD})
#        SET(C_INLINE TRUE)
#        ADD_DEFINITIONS("-Dinline=${KEYWORD}")
#      ENDIF(C_HAS_${KEYWORD})
#    ENDIF(NOT DEFINED C_INLINE)
#  ENDFOREACH(KEYWORD)
#
#  IF(NOT DEFINED C_INLINE)
#    ADD_DEFINITIONS("-Dinline=")
#  ENDIF(NOT DEFINED C_INLINE)
#endmacro(nugat_check_inline)


#-----------------------------------------------------------------------------
# Python support
#-----------------------------------------------------------------------------
include(FindPythonInterp)
if(NOT PYTHONINTERP_FOUND)
    message(FATAL_ERROR "Python not found, impossible to build ${CMAKE_PROJECT_NAME}")
endif()

# get the python version
execute_process(COMMAND ${PYTHON_EXECUTABLE} --version
    OUTPUT_VARIABLE PYTHON_version_output
    ERROR_VARIABLE PYTHON_version_output
    RESULT_VARIABLE PYTHON_version_result
    OUTPUT_STRIP_TRAILING_WHITESPACE)
if(NOT ${PYTHON_version_result} EQUAL 0)
    message(FATAL_ERROR "Command \"${PYTHON_EXECUTABLE} --version\" failed with output:\n${FLEX_version_error}")
else()
    string(REGEX REPLACE "^Python (.*)$" "\\1"
      PYTHON_VERSION "${PYTHON_version_output}")
endif()

# check python version
macro(nugat_check_python_version vn)
    if("${PYTHON_VERSION}" VERSION_LESS "${vn}")
        message(FATAL_ERROR "Python version too old: ${PYTHON_VERSION} (2.6.0 required)")
    endif()
endmacro()


#-----------------------------------------------------------------------------
# misc utility macros
#-----------------------------------------------------------------------------

macro(nugat_invalidate_find_var var value)
    if(NOT "${${var}--FLAG}" STREQUAL "${value}")
        set(${var}--FLAG "${value}" CACHE INTERNAL "")
        set(${var} NOTFOUND)
    endif()
endmacro()

# custom version of find_path that monitors the value of a user-provided path
#macro(nugat_find_path result name dir)
#    nugat_invalidate_find_var(${result} "${dir}")
#    find_path(${result} "${name}" "${dir}")
#endmacro()

# custom version of find_library that monitors the value of a user-provided path
macro(nugat_find_library result name dir)
    nugat_invalidate_find_var(${result} "${dir}")
    find_library(${result} "${name}" "${dir}")
endmacro()

# macro to add a build-time target that simply copies a file
#macro(nugat_add_copy_target dst src)
#    add_custom_command(OUTPUT ${dst}
#      COMMAND ${CMAKE_COMMAND} -E copy_if_different "${src}" "${dst}" VERBATIM
#      COMMENT "Copying ${src} to ${dst}"
#      ${ARGN})
#endmacro()

# macro to generate a timestamp string (using Python for portability)
macro(nugat_get_current_time dst)
    execute_process(COMMAND ${PYTHON_EXECUTABLE} -c
      "import sys, time; sys.stdout.write(time.asctime())"
      OUTPUT_VARIABLE ${dst})
endmacro()

# generates an autoconf-compatible HAVE_A_B_H from a name like a/b.h
macro(nugat_make_have_var name result)
    string(REGEX REPLACE "[/.]" "_" ${result} ${name})
    string(TOUPPER ${${result}} ${result})
    set(${result} "HAVE_${${result}}")
endmacro()

# checks that two paths are actually the same
#macro(nugat_same_path a b res)
#    get_filename_component(_a ${a} ABSOLUTE)
#    get_filename_component(_b ${b} ABSOLUTE)
#    if(${_a} STREQUAL ${_b})
#        set(${res} 1)
#    else()
#        set(${res} 0)
#    endif()
#endmacro()

# custom version of add_executable, does two extra things:
# 1. puts the executable in a bin/ directory (to avoid potential clashes
#    with dir names)
# 2. makes sure that C++ is used for linking, so that libstdc++ is linked
#    (needed e.g. when linking against the SAT solvers or mathsat)

#macro(nugat_add_executable name)
#    add_executable(${name} ${ARGN})
#    set_target_properties(${name} PROPERTIES
#      LINKER_LANGUAGE CXX
#      RUNTIME_OUTPUT_DIRECTORY "${PROJECT_BINARY_DIR}/bin"
#      )
#    install(TARGETS ${name} DESTINATION bin)
#endmacro()

#-----------------------------------------------------------------------------
# grammar generation macros
#-----------------------------------------------------------------------------
find_package(FLEX)
find_package(BISON)

if(NOT FLEX_FOUND)
    message(FATAL_ERROR "Flex is required")
endif()

if(NOT BISON_FOUND)
    message(FATAL_ERROR "Bison is required")
endif()

# custom command for generating a combined flex source file from components
macro(nugat_combine_scanner output)
    add_custom_command(OUTPUT "${output}"
      COMMAND ${PYTHON_EXECUTABLE}
      ARGS "${NUGAT_SOURCE_DIR}/cmake/nusmv/combine_grammar.py"
      "--output" "${output}" ${ARGN}
      DEPENDS ${ARGN} "${NUGAT_SOURCE_DIR}/cmake/nusmv/combine_grammar.py"
      COMMENT "generating flex source ${output}"
      WORKING_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}"
      )
endmacro()


# custom command for generating a combined bison source file from components
macro(nugat_combine_grammar start output)
    add_custom_command(OUTPUT ${output}
      COMMAND ${PYTHON_EXECUTABLE}
      ARGS "${NUGAT_SOURCE_DIR}/cmake/nusmv/combine_grammar.py"
      "--output" ${output} "--start" ${start} ${ARGN}
      DEPENDS ${ARGN} "${NUGAT_SOURCE_DIR}/cmake/nusmv/combine_grammar.py"
      COMMENT "generating bison source ${output}"
      WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
      )
endmacro()


#-----------------------------------------------------------------------------
# NuGAT package handling
#-----------------------------------------------------------------------------
# get a reasonable name for the current package
macro(nugat_get_pkg_name outname)
    unset(${outname})
    file(TO_CMAKE_PATH ${CMAKE_CURRENT_SOURCE_DIR} _d)
    set(_d ${_d}/${ARGV1})
    file(RELATIVE_PATH _pth ${PROJECT_SOURCE_DIR} ${_d})
    string(REPLACE "/" "_" ${outname} "${_pth}")
endmacro()

# adds the given package to the given library
macro(nugat_add_pkg name corelib)
    add_library(${name} OBJECT ${ARGN})
    set_property(GLOBAL APPEND PROPERTY nugat_${corelib}_pkgs ${name})
endmacro()

#-----------------------------------------------------------------------------
# Tools package handling
#-----------------------------------------------------------------------------
# adds the given package to the given library
#macro(tool_add_pkg tool name corelib)
#    add_library(${name} OBJECT ${ARGN})
#    set_property(GLOBAL APPEND PROPERTY ${tool}_${corelib}_pkgs ${name})
#endmacro()

#-----------------------------------------------------------------------------
# autoheader-like functionality
#-----------------------------------------------------------------------------

set_property(GLOBAL PROPERTY nugat_CONFIG_H_PREFIX "")

# sets a prefix for variables added to the config.h file
macro(nugat_set_config_h_prefix prefix)
    set_property(GLOBAL PROPERTY nugat_CONFIG_H_PREFIX
      "${prefix}")
endmacro()

# returns the name of the variable that is written in the config.h, according
# to the current prefix. Example: if the prefix is XXX_ and var is HAVE_VAR,
# returns XXX_HAVE_VAR
macro(nugat_get_config_h_name var result)
    get_property(_p GLOBAL PROPERTY nugat_CONFIG_H_PREFIX)
    set(${result} ${_p}${var})
endmacro()

# adds a 0/1 value variable to config.h
macro(nugat_add_config_h_01 var)
    set(_v ${${var}})
    if(${${var}})
        set(_v "1")
    else()
        set(_v "0")
    endif()
    nugat_get_config_h_name(${var} _n)
    set_property(GLOBAL APPEND_STRING
      PROPERTY nugat_CONFIG_H_VARS
      "\n#ifndef ${_n}\n#define ${_n} ${_v}\n#endif\n")
endmacro()

# sets the value for a 0/1 variable and adds it to config.h
macro(nugat_set_config_h_01 var value)
    set(${var} ${value})
    nugat_add_config_h_01(${var})
endmacro()

# adds a generic variable to config.h
macro(nugat_add_config_h var)
    set(_v ${${var}})
    nugat_get_config_h_name(${var} _n)
    set_property(GLOBAL APPEND_STRING
      PROPERTY nugat_CONFIG_H_VARS
      "\n#ifndef ${_n}\n#define ${_n} ${_v}\n#endif\n")
endmacro()

# sets the value of a generic variable and adds it to config.h
macro(nugat_set_config_h var value)
    set(${var} ${value})
    nugat_add_config_h(${var})
endmacro()

# adds a string variable to config.h
macro(nugat_add_config_h_str var)
    set(_v ${${var}})
    nugat_get_config_h_name(${var} _n)
    set_property(GLOBAL APPEND_STRING
      PROPERTY nugat_CONFIG_H_VARS
      "\n#ifndef ${_n}\n#define ${_n} \"${_v}\"\n#endif\n")
endmacro()

# sets the value of a string variable and adds it to config.h
macro(nugat_set_config_h_str var value)
    set(${var} ${value})
    nugat_add_config_h_str(${var})
endmacro()

# write the config.h to the file with the given name
macro(nugat_write_config_h name)
    get_property(_cfg GLOBAL PROPERTY nugat_CONFIG_H_VARS)
    nugat_get_current_time(_now)
    file(WRITE "${PROJECT_BINARY_DIR}/CMakeFiles/config.h"
      "/* Automatically generated by CMake ${CMAKE_VERSION} on ${_now} */
/* DO NOT EDIT (unless you know what you are doing) */
${_cfg}
")
    configure_file("${PROJECT_BINARY_DIR}/CMakeFiles/config.h"
                   "${PROJECT_BINARY_DIR}/${name}" COPYONLY)
endmacro()

## removes all the variables from the current config.h
#macro(nugat_clear_config_h)
#    nugat_set_config_h_prefix("")
#    set_property(GLOBAL PROPERTY nugat_CONFIG_H_VARS "")
#endmacro()


##-----------------------------------------------------------------------------
## Check for features
##-----------------------------------------------------------------------------
#
#include(CheckCSourceCompiles)
#include(CheckCXXSourceCompiles)
#include(CheckCSourceRuns)
#include(CheckTypeSize)
#include(CheckIncludeFile)
#include(CheckFunctionExists)
#include(CheckSymbolExists)
#
## check if the compiler supports the noreturn function attribute
#macro(nugat_check_funcattr_noreturn)
#    unset(FUNCATTR_NORETURN)
#    check_c_source_compiles("
#    __attribute__ ((noreturn)) void f(void) {}
#
#    int main(void)
#    {
#        f();
#        return 0;
#    }
#    "
#      _have_funcattr_noreturn
#      )
#    if(_have_funcattr_noreturn)
#        set(FUNCATTR_NORETURN "__attribute__ ((noreturn))")
#    endif()
#    nugat_add_config_h(FUNCATTR_NORETURN)
#endmacro()
#
#
## check if the compiler supports the __warn_unused_result__ function attribute
#macro(nugat_check_funcattr_warn_unused_result)
#    unset(GCC_WARN_UNUSED_RESULT)
#    check_c_source_compiles("
#    __attribute__ ((__warn_unused_result__)) int f(int i) { return i; }
#
#    int main(void)
#    {
#        f(1);
#        return 0;
#    }
#    "
#      _have_funcattr_warn_unused_result)
#    if(_have_funcattr_warn_unused_result)
#        set(GCC_WARN_UNUSED_RESULT "__attribute__ ((__warn_unused_result__))")
#    endif()
#    nugat_add_config_h(GCC_WARN_UNUSED_RESULT)
#endmacro()
#
## check for a suitable malloc implementation
#macro(nugat_check_malloc)
#    if(CMAKE_CROSSCOMPILING AND MINGW)
#        set(HAVE_MALLOC 1 CACHE INTERNAL "")
#    else()
#        check_c_source_runs("
#        char *malloc();
#
#        int main(void)
#        {
#            return (!malloc(0));
#        }
#        "
#          HAVE_MALLOC)
#        nugat_add_config_h_01(HAVE_MALLOC)
#
#        check_include_file(malloc.h _malloc_h_found)
#        if(_malloc_h_found)
#            set(HAVE_MALLOC_H 1)
#        else()
#            check_include_file(sys/malloc.h _malloc_h_found)
#            if(_malloc_h_found)
#                set(HAVE_SYS_MALLOC_H 1)
#            endif()
#        endif()
#        nugat_add_config_h_01(HAVE_MALLOC_H)
#        nugat_add_config_h_01(HAVE_SYS_MALLOC_H)
#        endif()
#endmacro()
#
## check for a given header file, and set the releated config.h var
#macro(nugat_check_header header)
#    nugat_make_have_var(${header} _h_found)
#    check_include_file(${header} ${_h_found})
#    nugat_add_config_h_01(${_h_found})
#endmacro()
#
## check for a given function, and set the related config.h var
#macro(nugat_check_function func)
#    set(_tmp ${CMAKE_REQUIRED_LIBRARIES})
#    if (!MSVC)
#        set(CMAKE_REQUIRED_LIBRARIES m)
#    endif()
#    nugat_make_have_var(${func} _func_found)
#    check_function_exists(${_func} ${_func_found})
#    nugat_add_config_h_01(${_func_found})
#    set(CMAKE_REQUIRED_LIBRARIES ${_tmp})
#endmacro()
#
## check for the C99 _Bool type
#macro(nugat_check_bool)
#    check_c_source_compiles("
#    #include <stdbool.h>
#    int main(void)
#    {
#        _Bool b;
#        return 0;
#    }
#    " HAVE__BOOL)
#    nugat_add_config_h_01(HAVE__BOOL)
#endmacro()
#
## check for the C preprocessor
#macro(nugat_check_cpp)
#    if(CMAKE_COMPILER_IS_GNUCC)
#        set(HAVE_CPP 1)
#        get_filename_component(_cpp "${CMAKE_C_COMPILER}" NAME)
#        set(PROG_CPP "${_cpp} -E -x c")
#    else()
#        find_program(HAVE_CPP cpp)
#        if(HAVE_CPP)
#            set(PROG_CPP "cpp -x c")
#        endif()
#    endif()
#    nugat_add_config_h_01(HAVE_CPP)
#    nugat_add_config_h_str(PROG_CPP)
#endmacro()
#
## check sizes of standard types, and set the related config.h vars
#macro(nugat_check_types_size)
#    check_type_size("int" SIZEOF_INT)
#    nugat_add_config_h(SIZEOF_INT)
#
#    check_type_size("long" SIZEOF_LONG)
#    nugat_add_config_h(SIZEOF_LONG)
#
#    check_type_size("long long" SIZEOF_LONG_LONG)
#    nugat_add_config_h(SIZEOF_LONG_LONG)
#
#    check_type_size("void *" SIZEOF_VOID_P)
#    nugat_add_config_h(SIZEOF_VOID_P)
#endmacro()
#
## check for common headers used in NuGAT, and set the related config.h vars
#macro(nugat_check_common_headers)
#    set(_required_headers
#      dirent.h
#      dlfcn.h
#      errno.h
#      errno.h
#      float.h
#      fnmatch.h
#      inttypes.h
#      limits.h
#      memory.h
#      ndir.h
#      regex.h
#      signal.h
#      stdbool.h
#      stddef.h
#      stdint.h
#      stdlib.h
#      string.h
#      strings.h
#      sys/dir.h
#      sys/ndir.h
#      sys/ioctl.h
#      sys/param.h
#      sys/resource.h
#      sys/signal.h
#      sys/stat.h
#      sys/time.h
#      sys/types.h
#      unistd.h
#      )
#    foreach(_h ${_required_headers})
#        nugat_check_header(${_h})
#    endforeach()
#endmacro()
#
## check for common functions used in NuGAT, and set the related config.h vars
#macro(nugat_check_common_functions)
#    set(_required_funcs
#      floor
#      getenv
#      getpid
#      isatty
#      memmove
#      memset
#      mkstemp
#      mktemp
#      popen
#      pow
#      random
#      realloc
#      setvbuf
#      srandom
#      strcasecmp
#      strchr
#      strrchr
#      strstr
#      strtod
#      strtol
#      strtoull
#      system
#      tmpnam
#      vprintf
#      )
#    foreach(_func ${_required_funcs})
#        nugat_check_function(${_func})
#    endforeach()
#endmacro()
#
#
## check for libxml2
#macro(nugat_find_libxml2 result includes libraries definitions)
#    set(${includes})
#    set(${libraries})
#    set(${definitions})
#
#    find_package(LibXml2)
#    if(NOT LIBXML2_FOUND)
#        set(${result} 0 CACHE INTERNAL "")
#    else()
#        set(${result} 1 CACHE INTERNAL "")
#        set(${libraries} ${${libraries}} ${LIBXML2_LIBRARIES})
#        set(${definitions} "${LIBXML2_DEFINITIONS}")
#        set(${includes} ${${includes}} "${LIBXML2_INCLUDE_DIR}")
#
#        find_package(PkgConfig)
#        if(PKG_CONFIG_FOUND)
#            set(_pths)
#            pkg_check_modules(_libxml2 QUIET libxml-2.0)
#            if(_libxml2_FOUND)
#                if(ENABLE_STATIC_LINK OR PREFER_STATIC_LIBRARIES)
#                    set(_pths ${_libxml2_STATIC_LIBRARY_DIRS})
#                    set(_libs ${_libxml2_STATIC_LIBRARIES})
#                else()
#                    set(_pths ${_libxml2_LIBRARY_DIRS})
#                    set(_libs ${_libxml2_LIBRARIES})
#                endif()
#                foreach(_l ${_libs})
#                    nugat_find_library(${_l}-pth "${_l}" "${_pths}")
#                    if(${_l}-pth)
#                        set(${libraries} ${${libraries}} ${${_l}-pth})
#                        message(STATUS "found xml2 library ${_l}: ${${_l}-pth}")
#                    else()
#                        message(FATAL_ERROR
#                                "Could not find required library: ${_l}")
#                    endif()
#                endforeach()
#            endif()
#        endif()
#
#        if(WIN32 AND CMAKE_COMPILER_IS_GNUCC)
#            foreach(_l ${LIBXML2_LIBRARIES})
#                get_filename_component(_p ${_l} NAME)
#                if("${_p}" STREQUAL "libxml2.a")
#                    set(${definitions} "${${definitions}} -DLIBXML_STATIC")
#                    break()
#                endif()
#            endforeach()
#        endif()
#
#        if(WIN32)
#            find_library(LIB_WS2_32 ws2_32)
#            if(LIB_WS2_32)
#                set(${libraries} ${${libraries}} "${LIB_WS2_32}")
#            endif()
#        endif()
#    endif()
#endmacro()
#
## custom package target
#macro(nugat_add_package_target)
#    set(CPACK_GENERATOR "TGZ")
#    set(CPACK_PACKAGE_NAME ${PACKAGE_NAME})
#    set(CPACK_PACKAGE_VERSION ${PACKAGE_VERSION})
#
#    include(CPack)
#endmacro()
#
#macro(nugat_add_uninstall_target)
#    file(WRITE "${PROJECT_BINARY_DIR}/cmake_uninstall.cmake"
#"if(NOT EXISTS \"${PROJECT_BINARY_DIR}/install_manifest.txt\")
#  message(FATAL_ERROR \"Cannot find install manifest: ${PROJECT_BINARY_DIR}/install_manifest.txt\")
#endif()
#
#file(READ \"${PROJECT_BINARY_DIR}/install_manifest.txt\" files)
#string(REGEX REPLACE \"\\n\" \";\" files \"\${files}\")
#set(alldirs)
#foreach(file \${files})
#  message(STATUS \"Uninstalling \$ENV{DESTDIR}\${file}\")
#  if(IS_SYMLINK \"\$ENV{DESTDIR}\${file}\" OR EXISTS \"\$ENV{DESTDIR}\${file}\")
#    execute_process(
#      COMMAND ${CMAKE_COMMAND} -E remove \"\$ENV{DESTDIR}\${file}\"
#      OUTPUT_VARIABLE rm_out
#      RESULT_VARIABLE rm_retval
#      )
#    if(NOT \${rm_retval} EQUAL 0)
#      message(FATAL_ERROR \"Problem when removing \$ENV{DESTDIR}\${file}\")
#    endif()
#    get_filename_component(pth \"\$ENV{DESTDIR}\${file}\" PATH)
#    while(NOT \"\${pth}\" STREQUAL \"\$ENV{DESTDIR}\")
#        set(alldirs \${alldirs} \"\${pth}\")
#        get_filename_component(pth \"\${pth}\" PATH)
#    endwhile()
#  else()
#    message(STATUS \"File \$ENV{DESTDIR}\${file} does not exist.\")
#  endif()
#endforeach()
#
#list(REMOVE_DUPLICATES alldirs)
#list(SORT alldirs)
#list(REVERSE alldirs)
#
#foreach(d \${alldirs})
#  unset(l)
#  file(GLOB l \"\${d}/*\")
#  if(NOT l AND IS_DIRECTORY \"\${d}\")
#      message(STATUS \"Removing empty directory \${d}\")
#      execute_process(
#        COMMAND ${CMAKE_COMMAND} -E remove_directory \"\${d}\"
#        OUTPUT_VARIABLE rm_out
#        RESULT_VARIABLE rm_retval
#      )
#      if(NOT \${rm_retval} EQUAL 0)
#          message(FATAL_ERROR \"Problem when removing \${d}\")
#      endif()
#  endif()
#endforeach()
#")
#
#    add_custom_target(uninstall
#        COMMAND ${CMAKE_COMMAND} -P
#        "${PROJECT_BINARY_DIR}/cmake_uninstall.cmake")
#endmacro()
