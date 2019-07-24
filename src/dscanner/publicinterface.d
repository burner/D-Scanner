module dscanner.publicinterface;

import dparse.parser;
import dparse.lexer;
import dparse.ast;
import dparse.rollback_allocator;
import std.algorithm;
import std.range;
import std.stdio;
import std.array;
import std.conv;
import std.typecons;
import containers.ttree;
import std.string;
import std.functional : toDelegate;
import std.typecons : Flag;

void genPublicInterface(string[] fileNames) {
	import std.stdio;

	PublicMember[] mems;

	TTree!string tags;
	LexerConfig config;
	StringCache cache = StringCache(StringCache.defaultBucketCount);
	foreach (fileName; fileNames)
	{
		RollbackAllocator rba;

		ubyte[] bytes;

		if (fileName == "stdin")
		{
			File f = std.stdio.stdin;
			immutable stepSize = 4096;
			ubyte[] buffer = uninitializedArray!(ubyte[])(stepSize);

			while (true)
			{
				auto dataRead = f.rawRead(buffer[$ - stepSize .. $]);
				if (dataRead.length < stepSize)
				{
					bytes = buffer[0 .. $ - (stepSize - dataRead.length)];
					break;
				}
				buffer.length += stepSize;
			}
		}
		else
		{
			File f = File(fileName);

			if (f.size == 0)
				continue;

			bytes = uninitializedArray!(ubyte[])(to!size_t(f.size));
			f.rawRead(bytes);
		}

		auto tokens = getTokensForParser(bytes, config, &cache);
		Module m = parseModule(tokens.array, fileName, &rba, toDelegate(&doNothing));

		auto pubinter = new PublicInterface(&tags, &mems);
		pubinter.fileName = fileName;
		pubinter.visit(m);
	}
	//tags[].copy(stdout.lockingTextWriter);
}

private:

alias Public = Flag!"Public";

struct PublicMember {
	string[] path;
	Public isPublic;
}

enum AccessState
{
	Reset, /// when ascending the AST reset back to the previous access.
	Keep /// when ascending the AST keep the new access.
}

struct ContextType {
	string c;
	string access;
}

struct Entry {
	string name;
	string[] path;
	string access;
	string type;
	string sig;
	string[] argTypes;
	string[] tempArgTypes;
}


string whateverToString(T)(const T t)
{
	import dparse.formatter : Formatter;

	auto app = appender!string();
	auto formatter = new Formatter!(typeof(app))(app);
	formatter.format(t);
	return app.data;
}

struct TemplateParameterAppender {
	string[] data;

    void format(const TemplateParameter templateParameter)
    {
        debug(verbose) writeln("TemplateParameter");

        with(templateParameter)
        {
            if (templateTypeParameter)
                this.data ~= whateverToString(templateTypeParameter);
            else if (templateValueParameter)
                this.data ~= whateverToString(templateValueParameter);
            else if (templateAliasParameter)
                this.data ~= whateverToString(templateAliasParameter);
            else if (templateTupleParameter)
                this.data ~= whateverToString(templateTupleParameter);
            else if (templateThisParameter)
                this.data ~= whateverToString(templateThisParameter);
        }
    }

    void format(const TemplateParameterList templateParameterList)
    {
        foreach(i, param; templateParameterList.items)
        {
            this.data ~= whateverToString(param);
        }
    }

    void format(const TemplateParameters templateParameters)
    {
        debug(verbose) writeln("TemplateParameters");

        with(templateParameters)
        {
            if (templateParameterList)
                format(templateParameterList);
        }
    }
}

struct ParameterAppender {
	string[] data;

    void format(const Parameters parameters) {
        foreach (count, param; parameters.parameters)
        {
            format(param);
        }
        if (parameters.hasVarargs)
        {
            this.data ~= "...";
        }
    }

    void format(const Parameter parameter)
    {
        if (parameter.type !is null) {
            this.data ~= whateverToString(parameter.type);
		}

        foreach(suffix; parameter.cstyle)
            this.data.back ~= whateverToString(suffix);

        if (parameter.default_)
        {
            this.data.back ~= " = ";
        }

        if (parameter.vararg)
            this.data.back ~= "...";
    }
}

string[] templateParameterList(Dec)(const Dec dec) {
	static if (is(Dec == FunctionDeclaration) || is(Dec == Constructor))
	{
		if(dec.templateParameters)
		{
			TemplateParameterAppender tpa;
			tpa.format(dec.templateParameters);
			return tpa.data;
		}
	}
	return cast(string[])[];
}

string[] parameterList(Dec)(const Dec dec) {
	static if (is(Dec == FunctionDeclaration) || is(Dec == Constructor))
	{
		ParameterAppender pa;
		pa.format(dec.parameters);
		return pa.data;
	}
	else static if (is(Dec == TemplateDeclaration))
	{
		TemplateParameterAppender tpa;
		tpa.format(dec.templateParameters);
		return tpa.data;
	} else {
		return cast(string[])[];
	}
}

string paramsToString(Dec)(const Dec dec)
{
	import dparse.formatter : Formatter;

	auto app = appender!string();
	auto formatter = new Formatter!(typeof(app))(app);

	static if (is(Dec == FunctionDeclaration) || is(Dec == Constructor))
	{
		formatter.format(dec.parameters);
	}
	else static if (is(Dec == TemplateDeclaration))
	{
		formatter.format(dec.templateParameters);
	}

	return app.data;
}

final class PublicInterface : ASTVisitor
{
	public this(TTree!string* output, PublicMember[]* interfaces)
	{
		this.tagLines = output;
		this.interfaces = interfaces;
	}

	override void visit(const ClassDeclaration dec)
	{
		if(!canFind(["private", "package"], context.access)) {
			tagLines.insert("%s\t%s\t%d;\"\tclass\t%s %s\n".format(dec.name.text,
					fileName, dec.name.line, context.c, context.access));
		}
		auto paramsList = parameterList(dec);
		auto tempList = templateParameterList(dec);
		this.entries ~= Entry(dec.name.text, this.curModule, context.access,
				"class", "", paramsList, tempList);
		immutable c = context;
		context = ContextType("\tclass:" ~ dec.name.text, "public");
		dec.accept(this);
		context = c;
	}

	override void visit(const StructDeclaration dec)
	{
		if (dec.name == tok!"")
		{
			dec.accept(this);
			return;
		}
		tagLines.insert("%s\t%s\t%d;\"\tstruct\t%s %s\n".format(dec.name.text,
				fileName, dec.name.line, context.c, context.access));

		auto paramsList = parameterList(dec);
		auto tempList = templateParameterList(dec);
		this.entries ~= Entry(dec.name.text, this.curModule, context.access,
				"struct", "", paramsList, tempList);
		this.curModule ~= dec.name.text;
		scope(exit) {
			this.curModule = this.curModule[0 .. $ - 1];
		}

		writeln(entries.back());
		immutable c = context;
		context = ContextType("\tstruct:" ~ dec.name.text, "public");
		dec.accept(this);
		context = c;
	}

	override void visit(const InterfaceDeclaration dec)
	{
		auto paramsList = parameterList(dec);
		auto tempList = templateParameterList(dec);
		tagLines.insert("%s\t%s\t%d;\"\tinterface\t%s %s\n".format(dec.name.text,
				fileName, dec.name.line, context.c, context.access));
		this.entries ~= Entry(dec.name.text, this.curModule, context.access,
				"interface", "", paramsList, tempList);
		writeln(entries.back());
		this.curModule ~= dec.name.text;
		scope(exit) {
			this.curModule = this.curModule[0 .. $ - 1];
		}
		immutable c = context;
		context = ContextType("\tinterface:" ~ dec.name.text, context.access);
		dec.accept(this);
		context = c;
	}

	override void visit(const TemplateDeclaration dec)
	{
		auto params = paramsToString(dec);
		auto paramsList = parameterList(dec);
		auto tempList = templateParameterList(dec);

		tagLines.insert("%s\t%s\t%d;\"\tTemplate\t%s %s\tsignature:%s\n".format(dec.name.text,
				fileName, dec.name.line, context.c, context.access, params));
		this.entries ~= Entry(dec.name.text, this.curModule, context.access, "template", "", paramsList, tempList);
		writeln(entries.back());
		this.curModule ~= dec.name.text;
		scope(exit) {
			this.curModule = this.curModule[0 .. $ - 1];
		}
		immutable c = context;
		context = ContextType("\ttemplate:" ~ dec.name.text, context.access);
		dec.accept(this);
		context = c;
	}

	override void visit(const FunctionDeclaration dec)
	{
		auto params = paramsToString(dec);
		auto paramsList = parameterList(dec);
		auto tempList = templateParameterList(dec);

		tagLines.insert("%s\t%s\t%d;\"\tfunction\t%s %s\tsignature:%s\n".format(dec.name.text,
				fileName, dec.name.line, context.c, context.access, params));
		this.entries ~= Entry(dec.name.text, this.curModule, context.access, "function", "", paramsList, tempList);
		writeln(entries.back(), paramsList, tempList);
	}

	override void visit(const Constructor dec)
	{
		auto params = paramsToString(dec);
		auto paramsList = parameterList(dec);
		auto tempList = templateParameterList(dec);

		tagLines.insert("this\t%s\t%d;\"\tconstructor\t%s\tsignature:%s %s\n".format(fileName,
				dec.line, context.c, params, context.access));
		this.entries ~= Entry("constructor", this.curModule, context.access, "constructor", "",
			paramsList, tempList);
		writeln(this.entries.back);
	}

	override void visit(const Destructor dec)
	{
		tagLines.insert("~this\t%s\t%d;\"\tdestructor\t%s\n".format(fileName,
				dec.line, context.c));
		this.entries ~= Entry("destructor", this.curModule, context.access, "destructor", "");
		writeln(this.entries.back);
	}

	override void visit(const EnumDeclaration dec)
	{
		tagLines.insert("%s\t%s\t%d;\"\tenum\t%s %s\n".format(dec.name.text,
				fileName, dec.name.line, context.c, context.access));
		immutable c = context;
		context = ContextType("\tenum:" ~ dec.name.text, context.access);
		this.entries ~= Entry(dec.name.text, this.curModule, context.access, "enum", "");
		writeln(this.entries.back);
		this.curModule ~= dec.name.text;
		scope(exit) {
			this.curModule = this.curModule[0 .. $ - 1];
		}
		dec.accept(this);
		context = c;
	}

	override void visit(const UnionDeclaration dec)
	{
		if (dec.name == tok!"")
		{
			dec.accept(this);
			return;
		}
		tagLines.insert("%s\t%s\t%d;\"\tunion\t %s\n".format(dec.name.text,
				fileName, dec.name.line, context.c));
		immutable c = context;
		context = ContextType("\tunion:" ~ dec.name.text, context.access);
		this.entries ~= Entry(dec.name.text, this.curModule, context.access, "union", "");
		writeln(this.entries.back);
		this.curModule ~= dec.name.text;
		scope(exit) {
			this.curModule = this.curModule[0 .. $ - 1];
		}
		dec.accept(this);
		context = c;
	}

	override void visit(const AnonymousEnumMember mem)
	{
		tagLines.insert("%s\t%s\t%d;\"\tenum_anon\t %s\n".format(mem.name.text,
				fileName, mem.name.line, context.c));
		this.entries ~= Entry(mem.name.text, this.curModule, context.access, "enum_anom", "");
		writeln(this.entries.back);
	}

	override void visit(const EnumMember mem)
	{
		tagLines.insert("%s\t%s\t%d;\"\tenum_member\t%s\n".format(mem.name.text,
				fileName, mem.name.line, context.c));
		this.entries ~= Entry(mem.name.text, this.curModule, context.access, "enum_member", "");
		writeln(this.entries.back);
	}

	override void visit(const VariableDeclaration dec)
	{
		foreach (d; dec.declarators)
		{
			tagLines.insert("%s\t%s\t%d;\"\tvariable\t%s %s\n".format(d.name.text,
					fileName, d.name.line, context.c, context.access));
			this.entries ~= Entry(d.name.text, this.curModule, context.access, "variable", "");
			writeln(this.entries.back);
		}
		dec.accept(this);
	}

	override void visit(const ModuleDeclaration dec)
	{
		context = ContextType("", "public");
		this.curModule = dec.moduleName.identifiers.map!(it => it.text.idup).array;
		dec.accept(this);
	}

	override void visit(const Attribute attribute)
	{
		if (attribute.attribute != tok!"")
		{
			switch (attribute.attribute.type)
			{
			case tok!"export":
				context.access = "public";
				break;
			case tok!"public":
				context.access = "public";
				break;
			case tok!"package":
				context.access = "protected";
				break;
			case tok!"protected":
				context.access = "protected";
				break;
			case tok!"private":
				context.access = "private";
				break;
			default:
			}
		}

		attribute.accept(this);
	}

	override void visit(const AttributeDeclaration dec)
	{
		accessSt = AccessState.Keep;
		dec.accept(this);
	}

	override void visit(const Declaration dec)
	{
		immutable c = context;
		dec.accept(this);

		final switch (accessSt) with (AccessState)
		{
		case Reset:
			context = c;
			break;
		case Keep:
			break;
		}
		accessSt = AccessState.Reset;
	}

	override void visit(const Unittest dec)
	{
		// skipping symbols inside a unit test to not clutter the ctags file
		// with "temporary" symbols.
		// TODO when phobos have a unittest library investigate how that could
		// be used to describe the tests.
		// Maybe with UDA's to give the unittest a "name".
	}

	override void visit(const AliasDeclaration dec)
	{
		// Old style alias
		if (dec.declaratorIdentifierList)
		{
			foreach (i; dec.declaratorIdentifierList.identifiers)
			{
				tagLines.insert("%s\t%s\t%d;\"\ta\tline:%d%s%s\n".format(i.text,
						fileName, i.line, i.line, context.c, context.access));
			}
		}
		dec.accept(this);
	}

	override void visit(const AliasInitializer dec)
	{
		tagLines.insert("%s\t%s\t%d;\"\ta\tline:%d%s%s\n".format(dec.name.text,
				fileName, dec.name.line, dec.name.line, context.c, context.access));

		dec.accept(this);
	}

	override void visit(const AliasThisDeclaration dec)
	{
		auto name = dec.identifier;
		tagLines.insert("%s\t%s\t%d;\"\ta\tline:%d%s%s\n".format(name.text,
				fileName, name.line, name.line, context.c, context.access));

		dec.accept(this);
	}

	alias visit = ASTVisitor.visit;
	string fileName;
	TTree!string* tagLines;
	ContextType context;
	AccessState accessSt;

	PublicMember[]* interfaces;
	string[] curModule;
	PublicMember current;

	Entry[] entries;
}

private void doNothing(string, size_t, size_t, string, bool)
{
}
