/** @file */ 
////////////////////////////////////////////////////////////////////////////////////////  
//    
//    This file is part of Boost Statechart Viewer.
//
//    Boost Statechart Viewer is free software: you can redistribute it and/or modify
//    it under the terms of the GNU General Public License as published by
//    the Free Software Foundation, either version 3 of the License, or
//    (at your option) any later version.
//
//    Boost Statechart Viewer is distributed in the hope that it will be useful,
//    but WITHOUT ANY WARRANTY; without even the implied warranty of
//    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
//    GNU General Public License for more details.
//
//    You should have received a copy of the GNU General Public License
//    along with Boost Statechart Viewer.  If not, see <http://www.gnu.org/licenses/>.
//
////////////////////////////////////////////////////////////////////////////////////////

//standard header files
#include <iostream>

//LLVM Header files
#include "llvm\Support\raw_ostream.h"
#include "llvm\Support\Host.h"
#include "llvm\Config\config.h"

//clang header files
#include "clang\Frontend\TextDiagnosticPrinter.h"
#include "clang\Lex\HeaderSearch.h"
#include "clang\Basic\FileManager.h"
#include "clang\Frontend\Utils.h"
#include "clang\Basic\TargetInfo.h"
#include "clang\Lex\Preprocessor.h"
#include "clang\Frontend\CompilerInstance.h"
#include "clang\AST\ASTConsumer.h"
#include "clang\Sema\Lookup.h"
#include "clang\Parse\ParseAST.h"
#include "clang\Basic\Version.h"
#include "clang\Driver\Driver.h"
#include "clang\Driver\Compilation.h"

//my own header files
#include "iooper.h"

using namespace clang;
using namespace clang::driver;
using namespace std;

/**
 * This class provides Simple diagnostic Client. It uses implementation in library for printing diagnostci information.
 * Also it counts number of warnings, errors, ... When an error occurs the program is stopped.
 */
class MyDiagnosticClient : public TextDiagnosticPrinter
{
	int nwarnings; /** Save number of Warnings occured during diagnostic */
	int nnotes;
	int nignored;
	int nerrors;
	public:
   /**
    * Initialize number of warnings, errors, ...
    */
   MyDiagnosticClient(llvm::raw_ostream &os, const DiagnosticOptions &diags, bool OwnsOutputStream = false):TextDiagnosticPrinter(os, diags, OwnsOutputStream = false)
	{
		nwarnings=0;
		nnotes=0;
		nignored=0;
		nerrors = 0;
	}
   /**
     * This method prints diagnostic and counts diagnostic types.
     */
	virtual void HandleDiagnostic(Diagnostic::Level DiagLevel, const DiagnosticInfo &Info)
	{
		TextDiagnosticPrinter::HandleDiagnostic(DiagLevel, Info); // print diagnostic information using library implementation
		switch (DiagLevel) // count number of all diagnostic information
		{
			case 0 : nignored+=1; break;
			case 1 : nnotes+=1; break;
			case 2 : nwarnings+=1; break;
			default : nerrors+=1; 
						 print_stats(); 
						 exit(1);
		}
	}
   /**
     * Print statistics about diagnostic.
     */
	void print_stats()
	{
		cout<<"\n--Diagnostic Info--\n";
		cout<<"Number of ignored: "<<nignored<<"\n";
		cout<<"Number of notes: "<<nnotes<<"\n";
		cout<<"Number of warnings: "<<nwarnings<<"\n";
		cout<<"Number of errors and fatal errors: "<<nerrors<<"\n";
	}
	
	int getNbrOfWarnings() /** Return number of warnings */
	{
		return nwarnings;		
	}
	
	int getNbrOfNotes() /** Return number of notes */
	{
		return nnotes;		
	}

	int getNbrOfIgnored() /** Return number of ignored */
	{
		return nignored;		
	}
};

/**
 * My ASTConsumer provides interface for traversing AST. It uses recursive traversing in namespaces.
 */
class FindStates : public ASTConsumer
{
	list<string> transitions; 
	list<string> cReactions; /** list of custom reactions. After all files are traversed this list should be empty. */
	list<string> events;
	list<string> states;
	string name_of_machine;
	string name_of_start;
	FullSourceLoc *fsloc; /** Full Source Location instance for holding Source Manager. */
	public:

	list<string> getStates() /** Return list of states. */
	{
		return states;
	}
	
	list<string> getTransitions() /** Return list of transitions. */
	{
		return transitions;
	}
		
	list<string> getEvents() /** Return list of events. */
	{
		return events;
	}

	string getStateMachine() /** Return name of the state machine. */
	{
		return name_of_machine;
	}

	string getNameOfFirstState() /** Return name of start state. */
	{
		return name_of_start;
	}
	
	virtual void Initialize(ASTContext &ctx)/** Run after the AST is constructed before the consumer starts to work. So this function works like constructor. */
	{	
		fsloc = new FullSourceLoc(* new SourceLocation(), ctx.getSourceManager());
		name_of_start = "";
		name_of_machine = "";
	}

/**
*   Traverse global decls using DeclGroupRef for handling all global decls. But only interesting decls are processed. Interesting decls are Struct, Class, C++ methods and Namespace.
*   When Namespace is found it recursively traverse all decls inside this Namespace using method recursive_visit.
*/
	virtual void HandleTopLevelDecl(DeclGroupRef DGR)
	{
		SourceLocation loc;
		string line, output, event;
		llvm::raw_string_ostream x(output);
		for (DeclGroupRef::iterator i = DGR.begin(), e = DGR.end(); i != e; ++i) 
		{
			const Decl *decl = *i;
			loc = decl->getLocation();
			if(loc.isValid())
			{
				if(decl->getKind()==35)
				{					
					method_decl(decl);
				}
				if (const TagDecl *tagDecl = dyn_cast<TagDecl>(decl))
				{
					if(tagDecl->isStruct() || tagDecl->isClass()) //is it a struct or class	
					{
						struct_class(decl);
					}
				}	
				if(const NamespaceDecl *namespaceDecl = dyn_cast<NamespaceDecl>(decl))
				{
					
					DeclContext *declCont = namespaceDecl->castToDeclContext(namespaceDecl);
					recursive_visit(declCont);
				
				}
			}
			output = "";
		}
	}

/**
*   It is used to recursive traverse decls in Namespaces. This method do the same as HandleTopLevelDecl.
*/
	void recursive_visit(const DeclContext *declCont)
	{
		string line, output, event;
		llvm::raw_string_ostream x(output);
		SourceLocation loc;
		for (DeclContext::decl_iterator i = declCont->decls_begin(), e = declCont->decls_end(); i != e; ++i)
		{
			const Decl *decl = *i;
			loc = decl->getLocation();
			if(loc.isValid())
			{	
				if(decl->getKind()==35)
				{
					method_decl(decl);
				}
				else if (const TagDecl *tagDecl = dyn_cast<TagDecl>(decl))
				{
					if(tagDecl->isStruct() || tagDecl->isClass()) //is it a structure or class	
					{
						struct_class(decl);
					}	
				}
				else if(const NamespaceDecl *namespaceDecl = dyn_cast<NamespaceDecl>(decl))
				{
					DeclContext *declCont = namespaceDecl->castToDeclContext(namespaceDecl);			
					recursive_visit(declCont);
				}
			}
			output = "";
		} 
	}
		
/**
*	This function works with class or struct. It splits the decl into 3 interesting parts.
*	The state machine decl, state decl and event decl.
*/
	void struct_class(const Decl *decl)
	{
		string output, line, ret, trans, event;	
		llvm::raw_string_ostream x(output);
		decl->print(x);
		line = get_line_of_code(x.str());
		output = "";
		int pos;
		const NamedDecl *namedDecl = dyn_cast<NamedDecl>(decl);
		if(is_derived(line))
		{
			const CXXRecordDecl *cRecDecl = dyn_cast<CXXRecordDecl>(decl);
					
			if(find_events(cRecDecl, line))
			{
				events.push_back(namedDecl->getNameAsString());
			}
			else if(name_of_machine == "")
			{
				ret = find_name_of_machine(cRecDecl, line);
				if(!ret.empty())
				{
					pos = ret.find(",");
					name_of_machine = ret.substr(0,pos);
					name_of_start = ret.substr(pos+1);
				}
			}
			else
			{
				ret = find_states(cRecDecl, line); 
				if(!ret.empty())
				{
					states.push_back(ret);			
					methods_in_class(decl,namedDecl->getNameAsString());
				}
			}
		}
	}

/**
*	This function provides traversing all methods and other context indide class. If
*	typedef or classic method decl is found. If typedef is found then it is being testted for transitions and custom reactions.
*/
	void methods_in_class(const Decl *decl, const string state)
	{
		string output, line, ret, trans, event;	
		llvm::raw_string_ostream x(output);
		int pos, num;
		const TagDecl *tagDecl = dyn_cast<TagDecl>(decl);
		const DeclContext *declCont = tagDecl->castToDeclContext(tagDecl);			
		output="";
		for (DeclContext::decl_iterator i = declCont->decls_begin(), e = declCont->decls_end(); i != e; ++i) 
		{
			if (i->getKind()==26) // typedefs
			{
				i->print(x);
				output = x.str();
				line = clean_spaces(cut_type(output));		
				ret = find_transitions(state,line);
				if(!ret.empty()) 
				{
					num = count(ret,';')+1;
					for(int i = 0;i<num;i++)
					{
						pos = ret.find(";");
						if(pos == 0)
						{
							ret = ret.substr(1);
							pos = ret.find(";");
							if(pos==-1) cReactions.push_back(ret);
							else cReactions.push_back(ret.substr(0,pos));	
							num-=1;
						}
						else 
						{
							if(pos==-1) transitions.push_back(ret);
							else transitions.push_back(ret.substr(0,pos));
						}
						if(i!=num-1) ret = ret.substr(pos+1);
					}
					output="";
				}
			}
			if(i->getKind()==35) method_decl(decl);// C++ method
		}
	}

 /**
   * Traverse method declaration using classes with main class Stmt.
   */
	void method_decl(const Decl *decl)
	{
		string output, line, event;	
		llvm::raw_string_ostream x(output);
		if(decl->hasBody())
		{
			decl->print(x);
			line = get_return(x.str());
			if(test_model(line,"result"))
			{
				const FunctionDecl *fDecl = dyn_cast<FunctionDecl>(decl);
				const ParmVarDecl *pvd = fDecl->getParamDecl(0);
                                QualType qt = pvd->getOriginalType();
				event = qt.getAsString();
				if(event[event.length()-1]=='&') event = event.substr(0,event.length()-2);
				event = event.substr(event.rfind(" ")+1);
				line = dyn_cast<NamedDecl>(decl)->getQualifiedNameAsString();
				line = cut_namespaces(line.substr(0,line.rfind("::")));
				line.append(",");
				line.append(event);
				find_return_stmt(decl->getBody(),line); 
				for(list<string>::iterator i = cReactions.begin();i!=cReactions.end();i++) // erase info about it from list of custom reactions
				{
					event = *i;
					if(line.compare(event)==0) 
					{
						cReactions.erase(i);
						break;
					}
				}
			}
		}
	}

	void find_return_stmt(Stmt *statemt,string event) /** Traverse all statements in function for finding all return Statements.*/
	{
		if(statemt->getStmtClass() == 99) test_stmt(dyn_cast<CaseStmt>(statemt)->getSubStmt(), event);
		else
		{
			for (Stmt::child_range range = statemt->children(); range; ++range)    
			{
				test_stmt(*range, event);
			}
		}
	}
	
	void test_stmt(Stmt *stmt, string event) /** test statement for its kind Using number as identifier for all Statement Classes.*/
	{
		const SourceManager &sman = fsloc->getManager();
		int type;
		string line, param;
		type = stmt->getStmtClass();
		switch(type)
		{	
			case 8 :		find_return_stmt(dyn_cast<DoStmt>(stmt)->getBody(), event); // do
							break;
			case 86 :	find_return_stmt(dyn_cast<ForStmt>(stmt)->getBody(), event); // for
							break;
			case 88 :   find_return_stmt(dyn_cast<IfStmt>(stmt)->getThen(), event); //if then
							find_return_stmt(dyn_cast<IfStmt>(stmt)->getElse(), event); //if else
							break;
			case 90 :	find_return_stmt(dyn_cast<LabelStmt>(stmt)->getSubStmt(), event); //label
							break;
			case 98 :	line = sman.getCharacterData(dyn_cast<ReturnStmt>(stmt)->getReturnLoc()); 
							line = get_line_of_code(line).substr(6);
							line = line.substr(0,line.find("("));
							if(test_model(line,"transit"))
							{
								param = get_params(line);
								transitions.push_back(event.append(",").append(param));
							}
							break;
			case 99 :  	find_return_stmt(stmt, event);
							break;
			case 101 : 	find_return_stmt(dyn_cast<SwitchStmt>(stmt)->getBody(), event); // switch
							break;
			case 102 : 	find_return_stmt(dyn_cast<WhileStmt>(stmt)->getBody(), event); // while
							break;
		}
	}

};
/**
  * Main function provides all initialization before starting analysis of AST. Diagnostic Client is initialized,
  * Command line options are processed.
  */
int main(int argc, char **argv)
{ 
	string inputFilename = "";
	string outputFilename = "graph.dot"; // initialize output Filename
	DiagnosticOptions dopts;
	dopts.ShowColors=1;
	MyDiagnosticClient *mdc = new MyDiagnosticClient(llvm::errs(), dopts);
	llvm::IntrusiveRefCntPtr<DiagnosticIDs> dis(new DiagnosticIDs());	
	Diagnostic diag(dis,mdc);
	FileManager fm( * new FileSystemOptions());
	SourceManager sm (diag, fm);
	HeaderSearch *headers = new HeaderSearch(fm);
	
	Driver TheDriver(LLVM_BINDIR, llvm::sys::getHostTriple(), "", false, false, diag);
	TheDriver.setCheckInputsExist(true);
	TheDriver.CCCIsCXX = 1;	
	TheDriver.ResourceDir = LLVM_PREFIX "\\lib\\clang\\" CLANG_VERSION_STRING;

	CompilerInvocation compInv;
	llvm::SmallVector<const char *, 16> Args(argv, argv + argc);
	llvm::OwningPtr<Compilation> C(TheDriver.BuildCompilation(Args.size(),
                                                            Args.data()));
	const driver::JobList &Jobs = C->getJobs();
	const driver::Command *Cmd = cast<driver::Command>(*Jobs.begin());
	const driver::ArgStringList &CCArgs = Cmd->getArguments();
	for(unsigned i = 0; i<Args.size();i++) // find -o in ArgStringList
	{	
		if(strncmp(Args[i],"-o",2)==0) 
		{
			if(strlen(Args[i])>2)
			{
				string str = Args[i];
				outputFilename = str.substr(2);
			}
			else outputFilename = Args[i+1];
			break;
		}
	}
		
	CompilerInvocation::CreateFromArgs(compInv,
	                                  const_cast<const char **>(CCArgs.data()),
	                                  const_cast<const char **>(CCArgs.data())+CCArgs.size(),
	                                  diag);

	HeaderSearchOptions hsopts = compInv.getHeaderSearchOpts();
	LangOptions lang = compInv.getLangOpts();
	CompilerInvocation::setLangDefaults(lang, IK_ObjCXX);
	TargetInfo *ti = TargetInfo::CreateTargetInfo(diag, compInv.getTargetOpts());
	FrontendOptions f = compInv.getFrontendOpts();
	inputFilename = f.Inputs[0].second;

	cout<<"Input filename: "<<inputFilename<<"\n"; // print Input filename
	cout<<"Output filename: "<<outputFilename<<"\n"; // print Output filename


	Preprocessor pp(diag, lang, *ti, sm, *headers);
	pp.getBuiltinInfo().InitializeBuiltins(pp.getIdentifierTable(), lang);
		
	InitializePreprocessor(pp, compInv.getPreprocessorOpts(),hsopts,f);
	
	const FileEntry *file = fm.getFile(inputFilename);
	sm.createMainFileID(file);
	IdentifierTable tab(lang);
	Builtin::Context builtins(*ti);
	FindStates c;
	ASTContext ctx(lang, sm, *ti, tab, * new SelectorTable(), builtins,0);
	mdc->BeginSourceFile(lang, &pp);//start using diagnostic
	ParseAST(pp, &c, ctx, false, false);
	mdc->EndSourceFile(); //end using diagnostic
	IO_operations *io = new IO_operations(outputFilename, c.getStateMachine(), c.getNameOfFirstState(), c.getTransitions(), c.getStates(), c.getEvents());
	io->save_to_file();
	io->print_stats();
	mdc->print_stats();
	return 0;
}