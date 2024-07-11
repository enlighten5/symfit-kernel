# This file is part of the SymCC runtime.
#
# The SymCC runtime is free software: you can redistribute it and/or modify it
# under the terms of the GNU Lesser General Public License as published by the
# Free Software Foundation, either version 3 of the License, or (at your option)
# any later version.
#
# The SymCC runtime is distributed in the hope that it will be useful, but
# WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
# FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General Public License
# for more details.
#
# You should have received a copy of the GNU Lesser General Public License along
# with the SymCC runtime. If not, see <https://www.gnu.org/licenses/>.

cmake_minimum_required(VERSION 3.16)
project(SymCCRuntime)

list(APPEND CMAKE_MODULE_PATH "${CMAKE_SOURCE_DIR}/cmake")

set(CMAKE_CXX_STANDARD 17)

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} \
-Wredundant-decls -Wcast-align \
-Wmissing-include-dirs -Wswitch-default \
-Wextra -Wall -Winvalid-pch -Wredundant-decls -Wformat=2 \
-Wmissing-format-attribute -Wformat-nonliteral")

set(SYMCC_RT_AVAILABLE_BACKENDS "simple" "qsym")
string(REPLACE ";" ", " SYMCC_RT_AVAILABLE_BACKENDS_FMT "\{${SYMCC_RT_AVAILABLE_BACKENDS}\}")

set(SYMCC_RT_BACKEND "qsym" CACHE STRING "SymCC Runtime Backend to build.\
Backends available: ${SYMCC_RT_AVAILABLE_BACKENDS_FMT}.")
option(Z3_TRUST_SYSTEM_VERSION "Use the system-provided Z3 without a version check" OFF)
set(LLVM_VERSION "" CACHE STRING "LLVM version to use. The corresponding LLVM dev package must be installed.")

# Place the final products in the top-level output directory
set(CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR})
set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR})

set(SYMCC_RT_SRC_DIR "${CMAKE_CURRENT_SOURCE_DIR}/src")
set(SYMCC_RT_INCLUDE_DIR "${CMAKE_CURRENT_SOURCE_DIR}/include")
set(SYMCC_RT_BACKEND_DIR "${SYMCC_RT_SRC_DIR}/backends/${SYMCC_RT_BACKEND}")

# There is list(TRANSFORM ... PREPEND ...), but it's not available before CMake 3.12.
set(SHARED_RUNTIME_SOURCES
  ${SYMCC_RT_SRC_DIR}/Config.cpp
  ${SYMCC_RT_SRC_DIR}/RuntimeCommon.cpp
  ${SYMCC_RT_SRC_DIR}/LibcWrappers.cpp
  ${SYMCC_RT_SRC_DIR}/Shadow.cpp
  ${SYMCC_RT_SRC_DIR}/GarbageCollection.cpp)

# Backends should produce two targets: SymCCRtStatic (static library) and SymCCRtShared (shared library).
add_subdirectory("${SYMCC_RT_BACKEND_DIR}")

message(STATUS "Using ${SYMCC_RT_BACKEND} backend.")

if (NOT TARGET SymCCRtStatic)
  message(FATAL_ERROR "The backend \"${SYMCC_RT_BACKEND}\" does not produce the target SymCCRtStatic.\
This is a bug and it should be reported. Please open PR to the symcc-rt repository.")
endif()

if (NOT TARGET SymCCRtShared)
  message(FATAL_ERROR "The backend \"${SYMCC_RT_BACKEND}\" does not produce the target SymCCRtShared.\
This is a bug and it should be reported. Please open PR to the symcc-rt repository.")
endif()

set_target_properties(SymCCRtStatic PROPERTIES OUTPUT_NAME "symcc-rt")
set_target_properties(SymCCRtShared PROPERTIES OUTPUT_NAME "symcc-rt")
