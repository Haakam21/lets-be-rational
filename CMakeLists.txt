cmake_minimum_required(VERSION 3.13)

set(PROJECT_NAME lets_be_rational)

project(${PROJECT_NAME} LANGUAGES CXX)

set(CMAKE_VERBOSE_MAKEFILE on)
set(CMAKE_CXX_COMPILER icpx)
set(CMAKE_CXX_STANDARD 17)

add_subdirectory(src)
