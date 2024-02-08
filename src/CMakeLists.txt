add_library(${PROJECT_NAME} STATIC erf_cody.cpp lets_be_rational.cpp dllmain.cpp normaldistribution.cpp rationalcubic.cpp)
target_compile_options(${PROJECT_NAME} PRIVATE -DNO_XL_API -Ofast -ffp-contract=fast -march=native)
