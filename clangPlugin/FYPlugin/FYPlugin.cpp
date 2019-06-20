
#include <iostream>
#include <vector>
#include <sstream>
#include <string>
#include "clang/AST/AST.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendPluginRegistry.h"
#include "llvm/Support/raw_ostream.h"
#include "clang/Sema/Sema.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Basic/Diagnostic.h"
#include "clang/AST/DeclObjC.h"

using namespace clang;
using namespace std;
using namespace llvm;
using namespace clang::ast_matchers;
/**
 RecursiveASTVisitor这是Clang用来以深度优先的方式遍历AST以及访问所有节点的工具类，
 支持前序遍历和后序遍历。它使用的是访问者模式。这个类依次做了3件事：
 遍历（Traverse）：遍历AST的每一个节点
 回溯（WalkUp）：在每一个节点上，从节点类型向上回溯直到节点的基类，然后再开始调用VisitXXX方法，父类型的Visit方法调用早于子类型的Visit方法调用。比如一个类型为NamespaceDecl的节点，调用Visit方法的顺序最终会是VisitDecl()->VisitNamedDecl()->VisitNamespaceDecl()。这种回溯机制保证了对于同一类型的节点被一起访问，防止不同类型节点的交替访问。
 访问（Visit）：对于每一个节点，如果用户重写了VisitXXX方法，则调用这个重写的Visit实现，否则使用基类默认的实现。
 
 */
static vector<string> split(const string &s, char delim){
    vector<string> elems;
    stringstream ss;
    ss.str(s);
    string item;
    while (getline(ss, item, delim)) {
        elems.push_back(item);
    }
    return elems;
}

namespace  {

    class FYPluginVisitor : public RecursiveASTVisitor<FYPluginVisitor>
    {
    private:
        CompilerInstance &Instance;
        ASTContext *Context;
        
    public:
        /**重写VisitObjCXXXDecl访问
        遍历所有的顶层子节点*/
        
        //访问类
        bool VisitObjCInterfaceDecl(ObjCInterfaceDecl *declaration)
        {
            if (isUserSourceCode(declaration))
            {
                checkClassNameForLowercaseName(declaration);
                checkClassNameForUnderscoreInName(declaration);
            }
            
            return true;
        }
        //访问方法
        bool VisitObjCMethodDecl(ObjCMethodDecl *declaration)
        {
            if (isUserSourceCode(declaration))
            {
                checkMethodNameForUppercaseName(declaration);
                checkMethodParamsNameForUppercaseName(declaration);
                checkMethodBodyForOver50Lines(declaration);
            }

            return true;
        }
        //访问属性
        bool VisitObjCPropertyDecl(ObjCPropertyDecl *declaration)
        {
            if (isUserSourceCode(declaration))
            {
                checkPropertyDecl(declaration);
                checkPropertyNameForUppercaseName(declaration);
                checkPropertyNameForUnderscoreInName(declaration);
                checkDelegatePropertyForUsageWeak(declaration);
            }

            return true;
        }
        //检测属性修饰符
        void checkPropertyDecl(const ObjCPropertyDecl *propertyDecl){
            if (propertyDecl) {
                ObjCPropertyDecl::PropertyAttributeKind attrKind = propertyDecl->getPropertyAttributes();
                string typeStr = propertyDecl->getType().getAsString();
                
                if (propertyDecl->getTypeSourceInfo() && isShouldUseCopy(typeStr) && !(attrKind & ObjCPropertyDecl::OBJC_PR_copy)) {
                    cout<<"--------- "<<typeStr<<": 不是使用的 copy 修饰--------"<<endl;
                    DiagnosticsEngine &diag = Instance.getDiagnostics();
                    diag.Report(propertyDecl->getBeginLoc(), diag.getCustomDiagID(DiagnosticsEngine::Warning, "--------- %0 不是使用的 copy 修饰--------")) << typeStr;
                }
            }
        }
        
        /**
         检测属性名是否存在大写开头
         
         @param decl 属性声明
         */
        void checkPropertyNameForUppercaseName(ObjCPropertyDecl *decl){
            bool checkUppercaseNameIndex = 0;
            StringRef name = decl -> getName();
            if (name.find('_') == 0)
            {
                //表示以下划线开头
                checkUppercaseNameIndex = 1;
            }
            //名称必须以小写字母开头
            char c = name[checkUppercaseNameIndex];
            if (isUppercase(c))
            {
                //修正提示
                std::string tempName = name;
                tempName[checkUppercaseNameIndex] = toLowercase(c);
                StringRef replacement(tempName);
                SourceLocation nameStart = decl->getLocation();
                SourceLocation nameEnd = nameStart.getLocWithOffset(name.size() - 1);
                FixItHint fixItHint = FixItHint::CreateReplacement(SourceRange(nameStart, nameEnd), replacement);
                //报告错误
                diagWaringReport(decl->getLocation(), "属性名不能以大写开头", &fixItHint);
            }
        }
        
        /**
         检测属性名是否包含下划线
         
         @param decl 属性声明
         */
        void checkPropertyNameForUnderscoreInName(ObjCPropertyDecl *decl){
            StringRef name = decl -> getName();
            
            if (name.size() == 1)
            {
                //不需要检测
                return;
            }
            
            //类名不能包含下划线
            size_t underscorePos = name.find('_', 1);
            if (underscorePos != StringRef::npos)
            {
                //修正提示
                std::string tempName = name;
                std::string::iterator end_pos = std::remove(tempName.begin() + 1, tempName.end(), '_');
                tempName.erase(end_pos, tempName.end());
                StringRef replacement(tempName);
                SourceLocation nameStart = decl->getLocation();
                SourceLocation nameEnd = nameStart.getLocWithOffset(name.size() - 1);
                FixItHint fixItHint = FixItHint::CreateReplacement(SourceRange(nameStart, nameEnd), replacement);
                //报告错误
                diagWaringReport(decl->getLocation(), "属性名字不允许有下划线", &fixItHint);
            }
        }
        
        /**
         检测委托属性是否有使用weak修饰
         
         @param decl 属性声明
         */
        void checkDelegatePropertyForUsageWeak (ObjCPropertyDecl *decl){
            QualType type = decl -> getType();
            StringRef typeStr = type.getAsString();
            
            //Delegate
            if(typeStr.find("<") != string::npos && typeStr.find(">") != string::npos)
            {
                ObjCPropertyDecl::PropertyAttributeKind attrKind = decl -> getPropertyAttributes();
                
                if(!(attrKind & ObjCPropertyDecl::OBJC_PR_weak))
                {
                    diagWaringReport(decl -> getLocation(), "代理属性应该使用weak修饰", NULL);
                }
            }
        }
        
       
        /**
         检测类名是否存在小写开头
         
         @param decl 类声明
         */
        void checkClassNameForLowercaseName(ObjCInterfaceDecl *decl){
            StringRef className = decl -> getName();
            
            //类名称必须以大写字母开头
            char c = className[0];
            if (isLowercase(c))
            {
                //修正提示
                std::string tempName = className;
                tempName[0] = toUppercase(c);
                StringRef replacement(tempName);
                SourceLocation nameStart = decl->getLocation();
                SourceLocation nameEnd = nameStart.getLocWithOffset(className.size() - 1);
                FixItHint fixItHint = FixItHint::CreateReplacement(SourceRange(nameStart, nameEnd), replacement);
                //报告警告
                diagWaringReport(decl->getLocation(), "类名不能以小写字母开头", &fixItHint);
            }
        }
        
        /**
         检测类名是否包含下划线
         
         @param decl 类声明
         */
        void checkClassNameForUnderscoreInName(ObjCInterfaceDecl *decl){
            StringRef className = decl -> getName();
            //类名不能包含下划线
            size_t underscorePos = className.find('_');
            if (underscorePos != StringRef::npos)
            {
                //修正提示
                std::string tempName = className;
                std::string::iterator end_pos = std::remove(tempName.begin(), tempName.end(), '_');
                tempName.erase(end_pos, tempName.end());
                StringRef replacement(tempName);
                SourceLocation nameStart = decl->getLocation();
                SourceLocation nameEnd = nameStart.getLocWithOffset(className.size() - 1);
                FixItHint fixItHint = FixItHint::CreateReplacement(SourceRange(nameStart, nameEnd), replacement);
                SourceLocation location = decl->getLocation().getLocWithOffset(underscorePos);
                diagWaringReport(location, "类名中不允许带有下划线", &fixItHint);
            }
        }
        
       
        /**
         检测方法名是否存在大写开头
         
         @param decl 方法声明
         */
        void checkMethodNameForUppercaseName(ObjCMethodDecl *decl){
            //检查名称的每部分，都不允许以大写字母开头
            Selector sel = decl -> getSelector();
            int selectorPartCount = decl -> getNumSelectorLocs();
            for (int i = 0; i < selectorPartCount; i++)
            {
                StringRef selName = sel.getNameForSlot(i);
                char c = selName[0];
                if (isUppercase(c))
                {
                    //修正提示
                    std::string tempName = selName;
                    tempName[0] = toLowercase(c);
                    StringRef replacement(tempName);
                    SourceLocation nameStart = decl -> getSelectorLoc(i);
                    SourceLocation nameEnd = nameStart.getLocWithOffset(selName.size() - 1);
                    FixItHint fixItHint = FixItHint::CreateReplacement(SourceRange(nameStart, nameEnd), replacement);
                    diagWaringReport(decl->getLocation(), "方法名不应该以大写开头", &fixItHint);
                }
            }
        }
        
        /**
         检测方法中定义的参数名称是否存在大写开头
         
         @param decl 方法声明
         */
        void checkMethodParamsNameForUppercaseName(ObjCMethodDecl *decl){
            for (ObjCMethodDecl::param_iterator it = decl -> param_begin(); it != decl -> param_end(); it++)
            {
                ParmVarDecl *parmVarDecl = *it;
                StringRef name = parmVarDecl -> getName();
                char c = name[0];
                if (isUppercase(c))
                {
                    //修正提示
                    std::string tempName = name;
                    tempName[0] = toLowercase(c);
                    StringRef replacement(tempName);
                    SourceLocation nameStart = parmVarDecl -> getLocation();
                    SourceLocation nameEnd = nameStart.getLocWithOffset(name.size() - 1);
                    FixItHint fixItHint = FixItHint::CreateReplacement(SourceRange(nameStart, nameEnd), replacement);
                    //报告警告
                    SourceLocation location = decl->getLocation();
                    diagWaringReport(location, "方法中定义的参数名不应该以大写开头", &fixItHint);
                }
            }
        }
        
        /**
         检测方法实现是否超过50行代码
         
         @param decl 方法声明
         */
        void checkMethodBodyForOver50Lines(ObjCMethodDecl *decl){
        if (decl -> hasBody())
        {
            //存在方法体
            Stmt *methodBody = decl -> getBody();
            
            string srcCode;
            srcCode.assign(Instance.getSourceManager().getCharacterData(methodBody->getSourceRange().getBegin()),
                            methodBody->getSourceRange().getEnd().getRawEncoding() - methodBody->getSourceRange().getBegin().getRawEncoding() + 1);
            vector<string> lines = split(srcCode, '\n');
            if(lines.size() > 50)
            {
                diagWaringReport(decl -> getSourceRange().getBegin(), "单个方法内行数不能超过50行", NULL);
            }
        }
    }
        /**
         判断是否为用户源码
         */
        bool isUserSourceCode (Decl *decl) {
        string filename =  Instance.getSourceManager().getFilename(decl->getSourceRange().getBegin()).str();
        
        if (filename.empty())
            return false;
        
        //非XCode中的源码都认为是用户源码
        if(filename.find("/Applications/Xcode.app/") == 0)
            return false;
        
        return true;
    }
        bool isShouldUseCopy(const string typeStr) {
            if (typeStr.find("NSString") != string::npos ||
                typeStr.find("NSArray") != string::npos ||
                typeStr.find("NSDictionary") != string::npos/*...*/) {
                return true;
            }
            return false;
        }
        template <unsigned N>
        //报告错误
        void diagWaringReport(SourceLocation Loc, const char (&FormatString)[N], FixItHint *Hint){
            DiagnosticsEngine &diagEngine = Instance.getDiagnostics();
            unsigned DiagID = diagEngine.getCustomDiagID(clang::DiagnosticsEngine::Warning, FormatString);
            (Hint!=NULL) ? diagEngine.Report(Loc, DiagID) << *Hint : diagEngine.Report(Loc, DiagID);
        }
        void setASTContext (ASTContext &context){
            this -> Context = &context;
        }
        
         FYPluginVisitor (CompilerInstance &Instance)
        :Instance(Instance),Context(&(Instance.getASTContext())) {}
    };
    
    //用于读取AST的抽象基类
    class FYASTConsumer: public ASTConsumer {
    private:
        FYPluginVisitor *visitor;
    public:
         FYASTConsumer(CompilerInstance &Instance)
        :visitor(new FYPluginVisitor(Instance)) {}
        
        virtual bool HandleTopLevelDecl(DeclGroupRef DG) override
        {
            return true;
        }
        
        virtual void HandleTranslationUnit(ASTContext& context) override
        {
            visitor->TraverseDecl(context.getTranslationUnitDecl());
        }
    
    };
    
    //AST的插件，同时也是访问ASTConsumer的入口
    class FYASTAction: public PluginASTAction {
        protected:
        /**重写CreateASTConsumer方法
         创建并返回给前端一个ASTConsumer
         */
        unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &Instance, StringRef iFile) {
            return unique_ptr<FYASTConsumer> (new FYASTConsumer(Instance));
        }
        //插件的入口函数
        bool ParseArgs(const CompilerInstance &Instance, const std::vector<std::string> &args) {
            return true;
        }
    };
}
//注册插件，指定Action
static FrontendPluginRegistry::Add<FYASTAction>
X("FYPlugin", "The FYPlugin is my first clang-plugin.");

