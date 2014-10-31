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

#include <iomanip>
#include <fstream>
#include <map>
#include <vector>
#include <iostream>

#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/raw_os_ostream.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Path.h"

#include "clang/AST/ASTConsumer.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/CXXInheritance.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendPluginRegistry.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Tooling.h"

namespace Model
{

inline int getIndentLevelIdx()
{
	static int i = std::ios_base::xalloc();
	return i;
}

std::ostream& indent(std::ostream& os)
{
	return os << std::setw(2 * os.iword(getIndentLevelIdx())) << "";
}

std::ostream& indent_inc(std::ostream& os)
{
	++os.iword(getIndentLevelIdx());
	return os;
}

std::ostream& indent_dec(std::ostream& os)
{
	--os.iword(getIndentLevelIdx());
	return os;
}

class State;

class Context: public std::map<std::string, State*>
{
public:
	iterator add(State *state);
	Context *findContext(const std::string &name);
};

class State: public Context
{
	std::string initialInnerState;
	std::list<std::string> defferedEvents;
	std::list<std::string> inStateEvents;
	bool noTypedef;

public:
	const std::string name;

	explicit State(std::string name) :
			noTypedef(false), name(std::move(name))
	{
	}

	void setInitialInnerState(std::string name)
	{
		initialInnerState = name;
	}

	void addDeferredEvent(const std::string &name)
	{
		defferedEvents.push_back(name);
	}

	void addInStateEvent(const std::string &name)
	{
		inStateEvents.push_back(name);
	}

	void setNoTypedef()
	{
		noTypedef = true;
	}

	friend std::ostream& operator<<(std::ostream& os, const State& s);
};

Context::iterator Context::add(State *state)
{
	return insert(value_type(state->name, state)).first;
}

Context *Context::findContext(const std::string &name)
{
	auto i = find(name);
	if (i != end())
		return i->second;

	for (auto& elem : *this)
	{
		Context *c = elem.second->findContext(name);
		if (c)
			return c;
	}

	return nullptr;
}

std::ostream& operator<<(std::ostream& os, const Context& c);

std::ostream& operator<<(std::ostream& os, const State& s)
{
	auto label = s.name;

	for (const auto & elem : s.defferedEvents)
		label.append("<br />").append(elem).append(" / defer");

	for (const auto & elem : s.inStateEvents)
		label.append("<br />").append(elem).append(" / in state");

	if (s.noTypedef)
		os << indent << s.name << " [label=<" << label << ">, color=\"red\"]\n";
	else
		os << indent << s.name << " [label=<" << label << ">]\n";

	if (s.size())
	{
		os << indent << s.name << " -> " << s.initialInnerState << " [style = dashed]\n";
		os << indent << "subgraph cluster_" << s.name << " {\n" << indent_inc;
		os << indent << "label = \"" << s.name << "\"\n";
		os << indent << s.initialInnerState << " [peripheries=2]\n";
		os << static_cast<Context>(s);
		os << indent_dec << indent << "}\n";
	}

	return os;
}

std::ostream& operator<<(std::ostream& os, const Context& c)
{
	for (const auto & elem : c)
	{
		os << *elem.second;
	}

	return os;
}

class Transition
{
public:
	const std::string src, dst, event;

	Transition(std::string src, std::string dst, std::string event) :
			src(std::move(src)), dst(std::move(dst)), event(std::move(event))
	{
	}
};

std::ostream& operator<<(std::ostream& os, const Transition& t)
{
	os << indent << t.src << " -> " << t.dst << " [label = \"" << t.event << "\"]\n";
	return os;
}

class Machine: public Context
{
protected:
	std::string initial_state;

public:
	const std::string name;

	explicit Machine(std::string name) :
			name(std::move(name))
	{
	}

	void setInitialState(std::string name)
	{
		initial_state = name;
	}

	friend std::ostream& operator<<(std::ostream& os, const Machine& m);
};

std::ostream& operator<<(std::ostream& os, const Machine& m)
{
	os << indent << "subgraph " << m.name << " {\n" << indent_inc;
	os << indent << m.initial_state << " [peripheries=2]\n";
	os << static_cast<Context>(m);
	os << indent_dec << indent << "}\n";
	return os;
}

class Model: public std::map<std::string, Machine>
{
	Context undefined;	// For forward-declared state classes

public:
	std::list<Transition*> transitions;

	iterator add(const Machine &m)
	{
		return insert(value_type(m.name, m)).first;
	}

	void addUndefinedState(State *m)
	{
		undefined[m->name] = m;
	}

	Context *findContext(const std::string &name)
	{
		auto ci = undefined.find(name);
		if (ci != undefined.end())
			return ci->second;

		auto i = find(name);
		if (i != end())
			return &i->second;

		for (auto& elem : *this)
		{
			if (auto c = elem.second.findContext(name))
				return c;
		}

		return nullptr;
	}

	State *findState(const std::string &name)
	{
		for (auto & elem : *this)
		{
			Context *c = elem.second.findContext(name);
			if (c)
				return static_cast<State*>(c);
		}

		return nullptr;
	}

	State *removeFromUndefinedContexts(const std::string &name)
	{
		auto ci = undefined.find(name);
		if (ci == undefined.end())
			return nullptr;
		undefined.erase(ci);
		return ci->second;
	}

	void write_as_dot_file(std::string const& fn)
	{
        std::cout << "Writing graph to '" << fn << "'.\n";

		std::ofstream f(fn);
		if (!f)
		{
	        std::cerr << "Failed to write file '" << fn << "'.\n";
	        std::exit(-1);
		}

		f << "digraph statecharts {\n" << indent_inc;

		for (auto& elem : *this)
			f << elem.second;

		for (auto& elem : transitions)
			f << *elem;

		f << indent_dec << "}\n";
	}
};

} // namespace Model

class MyCXXRecordDecl: public clang::CXXRecordDecl
{
	static bool FindBaseClassString(const clang::CXXBaseSpecifier *Specifier, clang::CXXBasePath &Path, void *qualName)
	{
		std::string qn(static_cast<const char*>(qualName));
		const clang::RecordType *rt = Specifier->getType()->getAs<clang::RecordType>();
		assert(rt);
		TagDecl *canon = rt->getDecl()->getCanonicalDecl();
		return canon->getQualifiedNameAsString() == qn;
	}

public:
	bool isDerivedFrom(const char *baseStr, clang::CXXBaseSpecifier const **Base = nullptr) const
	{
		clang::CXXBasePaths Paths(/*FindAmbiguities=*/false, /*RecordPaths=*/!!Base, /*DetectVirtual=*/false);
		Paths.setOrigin(const_cast<MyCXXRecordDecl*>(this));
		if (!lookupInBases(&FindBaseClassString, const_cast<char*>(baseStr), Paths))
			return false;
		if (Base)
			*Base = Paths.front().back().Base;
		return true;
	}
};

class FindTransitVisitor: public clang::RecursiveASTVisitor<FindTransitVisitor>
{
	Model::Model &model;
	const clang::CXXRecordDecl *SrcState;
	const clang::Type *EventType;

public:
	explicit FindTransitVisitor(Model::Model &model, const clang::CXXRecordDecl *SrcState, const clang::Type *EventType) :
			model(model), SrcState(SrcState), EventType(EventType)
	{
	}

	bool VisitMemberExpr(clang::MemberExpr *E)
	{
		if (E->getMemberNameInfo().getAsString() == "defer_event")
		{
			clang::CXXRecordDecl *Event = EventType->getAsCXXRecordDecl();

			Model::State *s = model.findState(SrcState->getName());
			assert(s);
			s->addDeferredEvent(Event->getName());
		}
		else if (E->getMemberNameInfo().getAsString() != "transit")
			return true;

		if (E->hasExplicitTemplateArgs())
		{
			const clang::Type *DstStateType = E->getExplicitTemplateArgs()[0].getArgument().getAsType().getTypePtr();
			clang::CXXRecordDecl *DstState = DstStateType->getAsCXXRecordDecl();
			clang::CXXRecordDecl *Event = EventType->getAsCXXRecordDecl();
			Model::Transition *T = new Model::Transition(SrcState->getName(), DstState->getName(), Event->getName());
			model.transitions.push_back(T);
		}

		return true;
	}
};

class Visitor: public clang::RecursiveASTVisitor<Visitor>
{
	struct eventModel
	{
		std::string name;
		clang::SourceLocation loc;

		eventModel(std::string ev, clang::SourceLocation sourceLoc) :
				name(std::move(ev)), loc(std::move(sourceLoc))
		{
		}
	};

	struct eventHasName
	{
		std::string eventName;

		eventHasName(std::string name) :
				eventName(std::move(name))
		{
		}

		bool operator()(const eventModel& model)
		{
			return (eventName.compare(model.name) == 0);
		}
	};

	clang::ASTContext *ASTCtx;
	Model::Model &model;
	clang::DiagnosticsEngine &Diags;
	unsigned diag_unhandled_reaction_type, diag_unhandled_reaction_decl, diag_found_state, diag_found_statemachine, diag_no_history, diag_missing_reaction, diag_warning;
	std::vector<bool> reactMethodInReactions; // Indicates whether i-th react method is referenced from typedef reactions.
	std::list<eventModel> unusedEvents;

public:
	bool shouldVisitTemplateInstantiations() const
	{
		return true;
	}

	explicit Visitor(clang::ASTContext *Context, Model::Model &model, clang::DiagnosticsEngine &Diags) :
			ASTCtx(Context), model(model), Diags(Diags)
	{
		diag_found_statemachine = Diags.getCustomDiagID(clang::DiagnosticsEngine::Note, "Found statemachine '%0'");
		diag_found_state = Diags.getCustomDiagID(clang::DiagnosticsEngine::Note, "Found state '%0'");
		diag_unhandled_reaction_type = Diags.getCustomDiagID(clang::DiagnosticsEngine::Error, "Unhandled reaction type '%0'");
		diag_unhandled_reaction_decl = Diags.getCustomDiagID(clang::DiagnosticsEngine::Error, "Unhandled reaction decl '%0'");
		diag_no_history = Diags.getCustomDiagID(clang::DiagnosticsEngine::Error, "History is not yet supported");
		diag_missing_reaction = Diags.getCustomDiagID(clang::DiagnosticsEngine::Error, "Missing react method for event '%0'");
		diag_warning = Diags.getCustomDiagID(clang::DiagnosticsEngine::Warning, "'%0' %1");
	}

	clang::DiagnosticBuilder Diag(clang::SourceLocation Loc, unsigned DiagID)
	{
		return Diags.Report(Loc, DiagID);
	}

	void checkAllReactMethods(const clang::CXXRecordDecl *SrcState)
	{
		unsigned i = 0;
		clang::IdentifierInfo& II = ASTCtx->Idents.get("react");
		clang::DeclContext::lookup_const_result ReactRes = SrcState->lookup(clang::DeclarationName(&II));

		for (clang::DeclContext::lookup_const_result::iterator it = ReactRes.begin(), end = ReactRes.end(); it != end; ++it, ++i)
		{
			if (i >= reactMethodInReactions.size() || reactMethodInReactions[i] == false)
			{
				clang::CXXMethodDecl *React = clang::dyn_cast<clang::CXXMethodDecl>(*it);
				Diag(React->getParamDecl(0)->getLocStart(), diag_warning) << React->getParamDecl(0)->getType().getAsString() << " missing in typedef reactions";
			}
		}
	}

	bool HandleCustomReaction(const clang::CXXRecordDecl *SrcState, const clang::Type *EventType)
	{
		unsigned i = 0;
		clang::IdentifierInfo& II = ASTCtx->Idents.get("react");
		// TODO: Lookup for react even in base classes - probably by using Sema::LookupQualifiedName()
		clang::DeclContext::lookup_const_result ReactRes = SrcState->lookup(clang::DeclarationName(&II));

		for (auto & ReactRe : ReactRes)
		{
			if (clang::CXXMethodDecl *React = clang::dyn_cast<clang::CXXMethodDecl>(ReactRe))
			{
				if (React->getNumParams() >= 1)
				{
					const clang::ParmVarDecl *p = React->getParamDecl(0);
					const clang::Type *ParmType = p->getType().getTypePtr();
					if (i == reactMethodInReactions.size())
						reactMethodInReactions.push_back(false);

					if (ParmType->isLValueReferenceType())
						ParmType = clang::dyn_cast<clang::LValueReferenceType>(ParmType)->getPointeeType().getTypePtr();

					if (ParmType == EventType)
					{
						FindTransitVisitor(model, SrcState, EventType).TraverseStmt(React->getBody());
						reactMethodInReactions[i] = true;
						return true;
					}
				}
				else
					Diag(React->getLocStart(), diag_warning) << React << "has not a parameter";
			}
			else
				Diag((ReactRe)->getSourceRange().getBegin(), diag_warning) << (ReactRe)->getDeclKindName() << "is not supported as react method";

			i++;
		}

		return false;
	}

	void HandleReaction(const clang::Type *T, const clang::SourceLocation Loc, clang::CXXRecordDecl *SrcState)
	{
		// TODO: Improve Loc tracking
		if (const clang::ElaboratedType *ET = clang::dyn_cast<clang::ElaboratedType>(T))
			HandleReaction(ET->getNamedType().getTypePtr(), Loc, SrcState);
		else if (const clang::TemplateSpecializationType *TST = clang::dyn_cast<clang::TemplateSpecializationType>(T))
		{
			auto name = TST->getTemplateName().getAsTemplateDecl()->getQualifiedNameAsString();
			if (name == "boost::statechart::transition")
			{
				const clang::Type *EventType = TST->getArg(0).getAsType().getTypePtr();
				const clang::Type *DstStateType = TST->getArg(1).getAsType().getTypePtr();
				clang::CXXRecordDecl *Event = EventType->getAsCXXRecordDecl();
				clang::CXXRecordDecl *DstState = DstStateType->getAsCXXRecordDecl();
				unusedEvents.remove_if(eventHasName(Event->getNameAsString()));

				Model::Transition *T = new Model::Transition(SrcState->getName(), DstState->getName(), Event->getName());
				model.transitions.push_back(T);
			}
			else if (name == "boost::statechart::custom_reaction")
			{
				const clang::Type *EventType = TST->getArg(0).getAsType().getTypePtr();
				if (!HandleCustomReaction(SrcState, EventType))
				{
					Diag(SrcState->getLocation(), diag_missing_reaction) << EventType->getAsCXXRecordDecl()->getName();
				}
				unusedEvents.remove_if(eventHasName(EventType->getAsCXXRecordDecl()->getNameAsString()));
			}
			else if (name == "boost::statechart::deferral")
			{
				const clang::Type *EventType = TST->getArg(0).getAsType().getTypePtr();
				clang::CXXRecordDecl *Event = EventType->getAsCXXRecordDecl();
				unusedEvents.remove_if(eventHasName(Event->getNameAsString()));

				Model::State *s = model.findState(SrcState->getName());
				assert(s);
				s->addDeferredEvent(Event->getName());
			}
			else if (name == "boost::mpl::list")
			{
				for (auto & elem : *TST)
					HandleReaction(elem.getAsType().getTypePtr(), Loc, SrcState);
			}
			else if (name == "boost::statechart::in_state_reaction")
			{
				const clang::Type *EventType = TST->getArg(0).getAsType().getTypePtr();
				clang::CXXRecordDecl *Event = EventType->getAsCXXRecordDecl();
				unusedEvents.remove_if(eventHasName(Event->getNameAsString()));

				Model::State *s = model.findState(SrcState->getName());
				assert(s);
				s->addInStateEvent(Event->getName());

			}
			else
				Diag(Loc, diag_unhandled_reaction_type) << name;
		}
		else
			Diag(Loc, diag_unhandled_reaction_type) << T->getTypeClassName();
	}

	void HandleReaction(const clang::NamedDecl *Decl, clang::CXXRecordDecl *SrcState)
	{
		if (const clang::TypedefDecl *r = clang::dyn_cast<clang::TypedefDecl>(Decl))
			HandleReaction(r->getCanonicalDecl()->getUnderlyingType().getTypePtr(), r->getLocStart(), SrcState);
		else
			Diag(Decl->getLocation(), diag_unhandled_reaction_decl) << Decl->getDeclKindName();
		checkAllReactMethods(SrcState);
	}

	clang::TemplateArgumentLoc getTemplateArgLoc(const clang::TypeLoc &T, unsigned ArgNum, bool ignore)
	{
		if (const auto ET = T.getAs<clang::ElaboratedTypeLoc>())
			return getTemplateArgLoc(ET.getNamedTypeLoc(), ArgNum, ignore);
		else if (const auto TST = T.getAs<clang::TemplateSpecializationTypeLoc>())
		{
			if (TST.getNumArgs() >= ArgNum + 1)
			{
				return TST.getArgLoc(ArgNum);
			}
			else if (!ignore)
				Diag(TST.getBeginLoc(), diag_warning) << TST.getType()->getTypeClassName() << "has not enough arguments" << TST.getSourceRange();
		}
		else
			Diag(T.getBeginLoc(), diag_warning) << T.getType()->getTypeClassName() << "type as template argument is not supported" << T.getSourceRange();

		return clang::TemplateArgumentLoc();
	}

	clang::TemplateArgumentLoc getTemplateArgLocOfBase(const clang::CXXBaseSpecifier *Base, unsigned ArgNum, bool ignore)
	{
		return getTemplateArgLoc(Base->getTypeSourceInfo()->getTypeLoc(), ArgNum, ignore);
	}

	clang::CXXRecordDecl *getTemplateArgDeclOfBase(const clang::CXXBaseSpecifier *Base, unsigned ArgNum, clang::TemplateArgumentLoc &Loc, bool ignore = false)
	{
		Loc = getTemplateArgLocOfBase(Base, ArgNum, ignore);
		switch (Loc.getArgument().getKind())
		{
		case clang::TemplateArgument::Type:
			return Loc.getTypeSourceInfo()->getType()->getAsCXXRecordDecl();
		case clang::TemplateArgument::Null:
			// Diag() was already called
			break;
		default:
			Diag(Loc.getSourceRange().getBegin(), diag_warning) << Loc.getArgument().getKind() << "unsupported kind" << Loc.getSourceRange();
		}
		return nullptr;
	}

	clang::CXXRecordDecl *getTemplateArgDeclOfBase(const clang::CXXBaseSpecifier *Base, unsigned ArgNum, bool ignore = false)
	{
		clang::TemplateArgumentLoc Loc;
		return getTemplateArgDeclOfBase(Base, ArgNum, Loc, ignore);
	}

	void handleSimpleState(clang::CXXRecordDecl *RecordDecl, const clang::CXXBaseSpecifier *Base)
	{
		int typedef_num = 0;
		std::string name(RecordDecl->getName()); //getQualifiedNameAsString());
		Diag(RecordDecl->getLocStart(), diag_found_state) << name;
		reactMethodInReactions.clear();

		Model::State *state;
		// Either we saw a reference to forward declared state
		// before, or we create a new state.
		if (!(state = model.removeFromUndefinedContexts(name)))
			state = new Model::State(name);

		clang::CXXRecordDecl *Context = getTemplateArgDeclOfBase(Base, 1);
		if (Context)
		{
			Model::Context *c = model.findContext(Context->getName());
			if (!c)
			{
				Model::State *s = new Model::State(Context->getName());
				model.addUndefinedState(s);
				c = s;
			}
			c->add(state);
		}
		//TODO support more innitial states
		clang::TemplateArgumentLoc Loc;
		if (MyCXXRecordDecl *InnerInitialState = static_cast<MyCXXRecordDecl*>(getTemplateArgDeclOfBase(Base, 2, Loc, true)))
		{
			if (InnerInitialState->isDerivedFrom("boost::statechart::simple_state") || InnerInitialState->isDerivedFrom("boost::statechart::state_machine"))
			{
				state->setInitialInnerState(InnerInitialState->getName());
			}
			else if (!InnerInitialState->getNameAsString().compare("boost::mpl::list<>"))
				Diag(Loc.getTypeSourceInfo()->getTypeLoc().getBeginLoc(), diag_warning) << InnerInitialState->getName() << " as inner initial state is not supported" << Loc.getSourceRange();
		}

// 	    if (CXXRecordDecl *History = getTemplateArgDecl(Base->getType().getTypePtr(), 3))
// 		Diag(History->getLocStart(), diag_no_history);

		clang::IdentifierInfo& II = ASTCtx->Idents.get("reactions");
		// TODO: Lookup for reactions even in base classes - probably by using Sema::LookupQualifiedName()
		clang::DeclContext::lookup_result Reactions = RecordDecl->lookup(clang::DeclarationName(&II));
		for (clang::DeclContext::lookup_result::iterator it = Reactions.begin(), end = Reactions.end(); it != end; ++it, typedef_num++)
			HandleReaction(*it, RecordDecl);

		if (typedef_num == 0)
		{
			Diag(RecordDecl->getLocStart(), diag_warning) << RecordDecl->getName() << "state has no typedef for reactions";
			state->setNoTypedef();
		}
	}

	void handleStateMachine(clang::CXXRecordDecl *RecordDecl, const clang::CXXBaseSpecifier *Base)
	{
		Model::Machine m(RecordDecl->getName());
		Diag(RecordDecl->getLocStart(), diag_found_statemachine) << m.name;

		if (MyCXXRecordDecl *InitialState = static_cast<MyCXXRecordDecl*>(getTemplateArgDeclOfBase(Base, 1)))
			m.setInitialState(InitialState->getName());

		model.add(m);
	}

	bool VisitCXXRecordDecl(clang::CXXRecordDecl *Declaration)
	{
		if (!Declaration->isCompleteDefinition())
			return true;

		if (Declaration->getQualifiedNameAsString() == "boost::statechart::state" || Declaration->getQualifiedNameAsString() == "TimedState" || Declaration->getQualifiedNameAsString() == "TimedSimpleState" || Declaration->getQualifiedNameAsString() == "boost::statechart::assynchronous_state_machine")
			return true; // This is an "abstract class" not a real state or real state machine

		MyCXXRecordDecl *RecordDecl = static_cast<MyCXXRecordDecl*>(Declaration);
		const clang::CXXBaseSpecifier *Base;

		if (RecordDecl->isDerivedFrom("boost::statechart::simple_state", &Base))
			handleSimpleState(RecordDecl, Base);
		else if (RecordDecl->isDerivedFrom("boost::statechart::state_machine", &Base))
			handleStateMachine(RecordDecl, Base);
		else if (RecordDecl->isDerivedFrom("boost::statechart::event"))
		{
			// Mark the event as unused until we found that somebody uses it
			unusedEvents.push_back(eventModel(RecordDecl->getNameAsString(), RecordDecl->getLocation()));
		}

		return true;
	}

	void printUnusedEventDefinitions()
	{
		for (auto& elem : unusedEvents)
			Diag((elem).loc, diag_warning) << (elem).name << "event defined but not used in any state";
	}
};

class VisualizeStatechartConsumer: public clang::ASTConsumer
{
public:
	explicit VisualizeStatechartConsumer(clang::ASTContext *Context, std::string destFileName, clang::DiagnosticsEngine &D) :
			visitor(Context, model, D), destFileName(std::move(destFileName))
	{
	}

private:
	void HandleTranslationUnit(clang::ASTContext &Context) override
	{
		visitor.TraverseDecl(Context.getTranslationUnitDecl());
		visitor.printUnusedEventDefinitions();
		model.write_as_dot_file(destFileName);
	}

private:
	Model::Model model;
	Visitor visitor;
	std::string destFileName;
};

static std::string abs_path;

class VisualizeStatechartAction: public clang::ASTFrontendAction
{
private:
	clang::ASTConsumer* CreateASTConsumer(clang::CompilerInstance &CI, llvm::StringRef) override
	{
		std::string dest = abs_path;
		dest += llvm::sys::path::stem(getCurrentFile());
		dest += ".dot";

		return new VisualizeStatechartConsumer(&CI.getASTContext(), dest, CI.getDiagnostics());
	}
};

static llvm::cl::OptionCategory visualizer_category("visualize options");
static llvm::cl::extrahelp common_help(clang::tooling::CommonOptionsParser::HelpMessage);

int main(int argc, const char **argv)
{
	using namespace clang::tooling;
	abs_path = getAbsolutePath("");
	CommonOptionsParser options_parser(argc, argv, visualizer_category);
	ClangTool tool(options_parser.getCompilations(), options_parser.getSourcePathList());
	return tool.run(newFrontendActionFactory<VisualizeStatechartAction>().get());
}
