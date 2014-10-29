# Copyright (c) 2014, Daniel Pfeifer <daniel@pfeifer-mail.de>
#
# Permission to use, copy, modify, and/or distribute this software for any
# purpose with or without fee is hereby granted, provided that the above
# copyright notice and this permission notice appear in all copies.
#
# THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
# WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
# MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
# ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
# WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
# ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
# OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.

cmake_minimum_required(VERSION 3.0)
project(BoostStatechartViewer CXX)

add_subdirectory(examples)

find_package(LLVM REQUIRED CONFIG)

set(CMAKE_EXE_LINKER_FLAGS "-static-libgcc -static-libstdc++")

add_executable(boost-statechart-viewer
  src/visualizer.cpp
  )

set_target_properties(boost-statechart-viewer PROPERTIES
  LINK_SEARCH_START_STATIC 1
  LINK_SEARCH_END_STATIC 1
  )

target_compile_options(boost-statechart-viewer PRIVATE
  -std=c++11
  )

target_compile_definitions(boost-statechart-viewer PRIVATE
  __STDC_CONSTANT_MACROS
  __STDC_LIMIT_MACROS
  )

target_link_libraries(boost-statechart-viewer PRIVATE
  clangTooling
  clangASTMatchers
  clangFrontend
  clangDriver
  LLVMOption
  clangParse
  LLVMMCParser
  clangSerialization
  clangSema
  clangEdit
  clangAnalysis
  LLVMBitReader
  clangRewrite
  clangAST
  clangLex
  clangBasic
  LLVMCore
  LLVMMC
  LLVMSupport
  )
