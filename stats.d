//          Copyright Brian Schott (Sir Alaran) 2012.
// Distributed under the Boost Software License, Version 1.0.
//    (See accompanying file LICENSE_1_0.txt or copy at
//          http://www.boost.org/LICENSE_1_0.txt)

module stats;

import std.stdio;
import std.algorithm;
import stdx.d.lexer;

pure nothrow bool isLineOfCode(IdType t)
{
	switch(t)
	{
	case tok!";":
	case tok!"while":
	case tok!"if":
	case tok!"do":
	case tok!"else":
	case tok!"switch":
	case tok!"for":
	case tok!"foreach":
	case tok!"foreach_reverse":
	case tok!"default":
	case tok!"case":
		return true;
	default:
		return false;
	}
}

ulong printTokenCount(Tokens)(File output, string fileName, ref Tokens tokens)
{
	ulong c = tokens.count!(a => true);
	output.writefln("%s:\t%d", fileName, c);
	return c;
}

ulong printLineCount(Tokens)(File output, string fileName, ref Tokens tokens)
{
	ulong count;
	foreach (t; tokens)
	{
		if (isLineOfCode(t.type))
			++count;
	}
	output.writefln("%s:\t%d", fileName, count);
	return count;
}
