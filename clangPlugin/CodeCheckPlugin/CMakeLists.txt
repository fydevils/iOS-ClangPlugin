
add_llvm_library(CodeCheckPlugin MODULE CodeCheckPlugin.cpp PLUGIN_TOOL clang)

 if(LLVM_ENABLE_PLUGINS AND (WIN32 OR CYGWIN))
   target_link_libraries(CodeCheckPlugin PRIVATE
     clangAST
     clangBasic
     clangFrontend
     LLVMSupport
     )
 endif()