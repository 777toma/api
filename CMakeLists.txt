cmake_minimum_required(VERSION 3.28)
project(api C)

add_compile_options(-Wno-unused-result)

set(CMAKE_C_STANDARD 11)

add_executable(api main.c)

target_link_libraries(api PRIVATE m)
