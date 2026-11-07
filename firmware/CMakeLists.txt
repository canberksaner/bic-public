cmake_minimum_required(VERSION 3.13)

set(CMAKE_C_STANDARD 11)
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

# Timing results must come from an optimized build.
if(NOT CMAKE_BUILD_TYPE)
    set(CMAKE_BUILD_TYPE Release)
endif()

# == DO NOT EDIT THE FOLLOWING LINES for the Raspberry Pi Pico VS Code Extension to work ==
if(WIN32)
    set(USERHOME $ENV{USERPROFILE})
else()
    set(USERHOME $ENV{HOME})
endif()
set(sdkVersion 2.3.1)
set(toolchainVersion 15_2_Rel1)
set(picotoolVersion 2.3.1)
set(picoVscode ${USERHOME}/.pico-sdk/cmake/pico-vscode.cmake)
if (EXISTS ${picoVscode})
    include(${picoVscode})
endif()
# ====================================================================================
set(PICO_BOARD pico2_w CACHE STRING "Board type")

include(pico_sdk_import.cmake)

project(pico_bic C CXX ASM)

pico_sdk_init()

# The firmware joins the network named in wifi_credentials.h.
if(NOT EXISTS ${CMAKE_CURRENT_LIST_DIR}/wifi_credentials.h)
    message(FATAL_ERROR "wifi_credentials.h not found: copy wifi_credentials.h.example "
                        "to wifi_credentials.h and fill in your network")
endif()

# BIC over WiFi (TCP port 4242), with firmware updates over WiFi (ota.c,
# A/B partitions of ota_pt.json).
add_executable(pico_bic_wifi main_wifi.c bic_service.c bic_core.c ota.c)
target_include_directories(pico_bic_wifi PRIVATE ${CMAKE_CURRENT_LIST_DIR})
# Keep the copies of a few per-group indices as inline loops: GCC would
# otherwise call memcpy for each of them in the solver's inner loops.
set_source_files_properties(bic_core.c PROPERTIES COMPILE_OPTIONS
                            "-fno-tree-loop-distribute-patterns")
target_link_libraries(pico_bic_wifi pico_stdlib pico_cyw43_arch_lwip_poll
                      pico_flash hardware_flash)

# USB serial for the status line (and picotool), UART off.
pico_enable_stdio_usb(pico_bic_wifi 1)
pico_enable_stdio_uart(pico_bic_wifi 0)

# Version from the configure time (major = 1000 * year-in-century +
# day of year, minor = minute of the day), so every build is newer than
# the last; scripts/pico_flash.py re-configures before each build.
string(TIMESTAMP BIC_YEAR "%y" UTC)
string(TIMESTAMP BIC_DAY "%j" UTC)
string(TIMESTAMP BIC_HOUR "%H" UTC)
string(TIMESTAMP BIC_MINUTE "%M" UTC)
math(EXPR BIC_FW_MAJOR "1000 * ${BIC_YEAR} + ${BIC_DAY}")
math(EXPR BIC_FW_MINOR "60 * ${BIC_HOUR} + ${BIC_MINUTE}")
pico_set_binary_version(pico_bic_wifi MAJOR ${BIC_FW_MAJOR} MINOR ${BIC_FW_MINOR})
file(WRITE ${CMAKE_BINARY_DIR}/pico_bic_wifi_version.txt "${BIC_FW_MAJOR}.${BIC_FW_MINOR}\n")

target_compile_definitions(pico_bic_wifi PRIVATE
    BIC_MAX_N=3500
    BIC_FW_MAJOR=${BIC_FW_MAJOR}
    BIC_FW_MINOR=${BIC_FW_MINOR}
    # Try before you buy: a new image runs once and must confirm itself.
    PICO_CRT0_IMAGE_TYPE_TBYB=1)
# The boot ROM checks this hash before running an image.
pico_hash_binary(pico_bic_wifi)
pico_add_extra_outputs(pico_bic_wifi)
