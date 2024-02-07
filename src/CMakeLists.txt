add_library(${PROJECT_NAME} STATIC erf_cody.cpp lets_be_rational.cpp dllmain.cpp normaldistribution.cpp rationalcubic.cpp)
target_include_directories(${PROJECT_NAME} PUBLIC $<BUILD_INTERFACE:${PROJECT_SOURCE_DIR}/include>)
target_compile_options(${PROJECT_NAME} PUBLIC -DNO_XL_API -Ofast -ffp-contract=fast -march=native)
