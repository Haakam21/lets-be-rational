add_library(${PROJECT_NAME} STATIC erf_cody.cpp lets_be_rational.cpp dllmain.cpp normaldistribution.cpp rationalcubic.cpp XLFunctions.cpp XLOper.cpp)
target_compile_options(${PROJECT_NAME} PUBLIC -DNDEBUG -fextended-identifiers -ffp-contract=fast -march=native -O3 -Ofast)
