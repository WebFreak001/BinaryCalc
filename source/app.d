import std.stdio : writeln, readln, writef, write, writefln;
import std.regex : StaticRegex, ctRegex, matchFirst;
import std.conv : to;
import std.string : strip, toUpper, toLower, split, join;
import std.uni : isAlpha;
import std.datetime : StopWatch;
static import std.file;
import core.exception : AssertError;
import std.random : uniform;
import number;

class SyntaxException : Exception {
	size_t position;

	public this(string msg, size_t pos) {
		super(msg ~ " at character " ~ to!string(pos));
		position = pos;
	}

	public override string toString() const {
		return this.msg;
	}
}

enum TokenType {
	Identifier,
	Number,
	BinNumber,
	HexNumber,
	ParenOpen,
	ParenClose,
	OpAdd,
	OpSub,
	OpMul,
	OpDiv,
	OpMod,
	OpAnd,
	OpOr,
	OpXor,
	OpPow,
	OpShiftL,
	OpShiftR,
	OpUShiftR,
	OpInvert,
	Equals,
	Unset,
}

struct Token {
	TokenType type;
	string content;
	size_t position;

	string toString() const {
		return content;
	}
}

private struct RegexToken {
	StaticRegex!char regex;
	TokenType type;
}

private static auto identifier = ctRegex!`^[a-zA-Z_][a-zA-Z_0-9]*`;

private static RegexToken[] tokenRegexes;

Token[] parseTokens(string expr) {

	if(tokenRegexes.length == 0) {
		tokenRegexes = [
			RegexToken(identifier, TokenType.Identifier),
			RegexToken(ctRegex!`^0b[01]+`, TokenType.BinNumber),
			RegexToken(ctRegex!`^0x[\da-fA-F]+`, TokenType.HexNumber),
			RegexToken(ctRegex!`^\d+`, TokenType.Number),
			RegexToken(ctRegex!`^(\^\^|\*\*)`, TokenType.OpPow),
			RegexToken(ctRegex!`^\(`, TokenType.ParenOpen),
			RegexToken(ctRegex!`^\)`, TokenType.ParenClose),
			RegexToken(ctRegex!`^\+`, TokenType.OpAdd),
			RegexToken(ctRegex!`^\-`, TokenType.OpSub),
			RegexToken(ctRegex!`^\*`, TokenType.OpMul),
			RegexToken(ctRegex!`^/`, TokenType.OpDiv),
			RegexToken(ctRegex!`^%`, TokenType.OpMod),
			RegexToken(ctRegex!`^&`, TokenType.OpAnd),
			RegexToken(ctRegex!`^\|`, TokenType.OpOr),
			RegexToken(ctRegex!`^\^`, TokenType.OpXor),
			RegexToken(ctRegex!`^<<`, TokenType.OpShiftL),
			RegexToken(ctRegex!`^>>>`, TokenType.OpUShiftR),
			RegexToken(ctRegex!`^>>`, TokenType.OpShiftR),
			RegexToken(ctRegex!`^~`, TokenType.OpInvert),
			RegexToken(ctRegex!`^=`, TokenType.Equals),
		];
	}

	Token[] tokens;
	size_t pos = 1;
	expr = expr.strip();
CodeLoop:
	while(expr.length > 0) {
		foreach(regex; tokenRegexes) {
			auto match = expr.matchFirst(regex.regex);
			if(!match.empty) {
				tokens ~= Token(regex.type, match.hit, pos);
				pos += match.hit.length;
				expr = expr[match.hit.length .. $].strip();
				continue CodeLoop;
			}
		}
		throw new SyntaxException("Unknown Identifier " ~ expr.start(10), pos);
	}
	return tokens;
}

string start(string str, int max) {
	if(str.length > max)
		return str[0 .. max - 3] ~ "...";
	return str;
}

enum Operator : ubyte {
	Add,
	Substract,
	Multiply,
	Divide,
	Modulo,
	And,
	Or,
	Xor,
	Pow,
	Bsr,
	UBsr,
	Bsl,
	UnaryPlus,
	UnaryMinus,
	UnaryInvert,
	Unset,
	Load,
}

enum ExpressionType {
	Number, Constant, Operator
}

struct LinearExpression {

	Operator operation;
	ExpressionType type;
	union {
		Number* number;
		string constant;
	}

	this(Operator operation) {
		this.operation = operation;
		this.type = ExpressionType.Operator;
	}

	this(string constant, Operator operation) {
		this.constant = constant;
		this.operation = operation;
		this.type = ExpressionType.Constant;
	}

	this(Number* number, Operator operation) {
		this.number = number;
		this.operation = operation;
		this.type = ExpressionType.Number;
	}
}

LinearExpression[] parseMathExpression(ref Token[] tokens) {
	LinearExpression[] expressions;
	Operator[] stack;

	if(tokens.length == 0)
		return [];

	bool inParen = false;

	if(tokens[0].type == TokenType.ParenOpen) {
		inParen = true;
		tokens = tokens[1 .. $];
	}

	TokenType previous = TokenType.ParenOpen;
	Token prevTok, initTok = tokens[0];
	bool closed = false;

	while(tokens.length > 0) {
		if(tokens[0].type == TokenType.BinNumber || tokens[0].type == TokenType.Number || tokens[0].type == TokenType.HexNumber || tokens[0].type == TokenType.Identifier) {
			if(!(previous != TokenType.BinNumber && previous != TokenType.Number && previous != TokenType.HexNumber && previous != TokenType.Identifier))
				throw new SyntaxException("Can't put 2 separate numbers behind each other", tokens[0].position);
			if(previous == TokenType.ParenClose)
				throw new SyntaxException("Can't continue with a number after parenthesis without an operator", tokens[0].position);
			if(tokens[0].type == TokenType.Identifier)
				expressions ~= LinearExpression(tokens[0].content, Operator.Load);
			else
				expressions ~= LinearExpression(new Number(tokens[0].content), Operator.Load);
			previous = tokens[0].type;
			prevTok = tokens[0];
			tokens = tokens[1 .. $];
			continue;
		}

		if(tokens[0].type == TokenType.ParenClose && inParen) {
			tokens = tokens[1 .. $];
			previous = TokenType.ParenClose;
			closed = true;
			break;
		}

		if(tokens[0].type == TokenType.ParenClose && !inParen) {
			throw new SyntaxException("Unmatched ')' (Parenthesis Close)", tokens[0].position);
		}

		if(tokens[0].type == TokenType.ParenOpen) {
			if(!(previous != TokenType.BinNumber && previous != TokenType.Number && previous != TokenType.HexNumber
				&& previous != TokenType.ParenClose))
					throw new SyntaxException("Parenthesis can't start here", tokens[0].position);
			previous = TokenType.ParenClose;
			expressions ~= parseMathExpression(tokens);
			continue;
		}

		Operator op = getOperator(tokens[0]);

		if(previous != TokenType.BinNumber && previous != TokenType.Number && previous != TokenType.HexNumber && previous != TokenType.Identifier
			&& previous != TokenType.ParenClose) {
			op = makeUnary(op);
			if(op == Operator.Unset)
				throw new SyntaxException("Operator can't be unary", tokens[0].position);
		}

		while(getPrecedence(op) <= getPrecedence(stack)) {
			expressions ~= LinearExpression(stack[$ - 1]);
			stack.length--;
		}

		stack ~= op;

		previous = tokens[0].type;
		prevTok = tokens[0];
		tokens = tokens[1 .. $];
	}

	if(inParen && !closed)
		throw new SyntaxException("Not closed group: '(' (Parenthesis Open)", initTok.position);

	if(!(previous == TokenType.BinNumber || previous == TokenType.Number || previous == TokenType.HexNumber
		|| previous == TokenType.Identifier || previous == TokenType.ParenClose))
		throw new SyntaxException("Invalid ending", prevTok.position);

	if(expressions.length == 0 && inParen)
		throw new SyntaxException("Empty group", initTok.position);

	while(stack.length > 0) {
		expressions ~= LinearExpression(stack[$ - 1]);
		stack.length--;
	}

	return expressions;
}

Operator makeUnary(Operator op) {
	switch(op) with(Operator) {
	case Add:
		return UnaryPlus;
	case Substract:
		return UnaryMinus;
	case UnaryInvert:
		return UnaryInvert;
	default:
		return Unset;
	}
}

Operator getOperator(Token token) {
	switch(token.type) with(TokenType) {
		case OpAdd:
			return Operator.Add;
		case OpSub:
			return Operator.Substract;
		case OpMul:
			return Operator.Multiply;
		case OpDiv:
			return Operator.Divide;
		case OpMod:
			return Operator.Modulo;
		case OpAnd:
			return Operator.And;
		case OpOr:
			return Operator.Or;
		case OpXor:
			return Operator.Xor;
		case OpPow:
			return Operator.Pow;
		case OpShiftL:
			return Operator.Bsl;
		case OpShiftR:
			return Operator.Bsr;
		case OpUShiftR:
			return Operator.UBsr;
		case OpInvert:
			return Operator.UnaryInvert;
		default:
			throw new SyntaxException("Unexpected Token (Expected Operator)", token.position);
	}
}

int getPrecedence(Operator[] operator) {
	if(operator.length == 0)
		return 0;

	return getPrecedence(operator[$ - 1]);
}

int getPrecedence(Operator operator) {
	switch(operator) with(Operator) {
	case Or:
		return 1;
	case Xor:
		return 2;
	case And:
		return 3;
	case Bsr:
	case UBsr:
	case Bsl:
		return 4;
	case Add:
	case Substract:
		return 5;
	case Multiply:
	case Divide:
	case Modulo:
		return 6;
	case Pow:
		return 7;
	case UnaryPlus:
	case UnaryMinus:
	case UnaryInvert:
		return 8;
	default:
		throw new Exception("Unknown Operator");
	}
}

Number calculate(LinearExpression[] expressions, Number[string] constants) {
	Number[] stack;
	foreach(expression; expressions) {
		switch(expression.type) {
		case ExpressionType.Constant:
			if((expression.constant.toUpper().strip() in constants) is null) {
				Number res;
				bool valid = false;
				while(!valid) {
					writef("Enter value for '%s': ", expression.constant.toUpper().strip());
					valid = parseExpression(res, readln(), false);
				}
				constants[expression.constant.toUpper().strip()] = res;
			}
			stack ~= constants[expression.constant.toUpper().strip()];
			break;
		case ExpressionType.Number:
			stack ~= *expression.number;
			break;
		case ExpressionType.Operator:
			switch(expression.operation) with(Operator) {
				case Add:
					stack[$ - 2] += stack[$ - 1];
					stack.length--;
					break;
				case Substract:
					stack[$ - 2] -= stack[$ - 1];
					stack.length--;
					break;
				case And:
					stack[$ - 2] &= stack[$ - 1];
					stack.length--;
					break;
				case Or:
					stack[$ - 2] |= stack[$ - 1];
					stack.length--;
					break;
				case Xor:
					stack[$ - 2] ^= stack[$ - 1];
					stack.length--;
					break;
				case Pow:
					stack[$ - 2] ^^= stack[$ - 1];
					stack.length--;
					break;
				case Bsr:
					stack[$ - 2] >>= stack[$ - 1];
					stack.length--;
					break;
				case UBsr:
					stack[$ - 2] >>>= stack[$ - 1];
					stack.length--;
					break;
				case Bsl:
					stack[$ - 2] <<= stack[$ - 1];
					stack.length--;
					break;
				case Multiply:
					stack[$ - 2] *= stack[$ - 1];
					stack.length--;
					break;
				case Divide:
					stack[$ - 2] /= stack[$ - 1];
					stack.length--;
					break;
				case Modulo:
					stack[$ - 2] %= stack[$ - 1];
					stack.length--;
					break;
				case UnaryPlus:
					break;
				case UnaryMinus:
					stack[$ - 1] = stack[$ - 1].negate();
					break;
				case UnaryInvert:
					stack[$ - 1] = stack[$ - 1].invert();
					break;
				default:
					throw new Exception("Unknown Operator");
			}
			break;
		default:
			break;
		}
	}
	return stack[0];
}

bool parseExpression(ref Number num, string expr, bool allowCommands = true) {
	expr = expr.strip();
	if(expr.length == 0)
		return false;
	if(isAlpha(expr[0]) && allowCommands) {
		auto args = expr.split(" ");
		const auto command = args[0];
	CommandLoop:
		switch(command) {
			case "help":
				writeln("Help for Binary Calculator:");
				writeln("Commands:");
				writeln("    help - Shows a help text");
				writeln("    bench <expr> - Benchmarks an expression");
				writeln("    dofile <file> - Runs every line in a file as input and outputs into <file>.out");
				writeln("    solve <expr> = <expr> - Tries to find the correct 'x' value from 2 linear expressions");
				writeln("    vars - Opens a global variable editor");
				writeln("");
				writeln("Operators: + - * / % & | ^ << >>");
				writeln("Start your input with '=' (equals sign) to mark it as math expression.");
				writeln("Name constants such as 'x' or 'width' to increase readability.");
				writeln("Global Constants:");
				writeln("    ans - Saves last result");
				writeln("    rndb - Random bit every time");
				writeln("    rnd - Random number between 0 and 32768 every time");
				break;
			case "bench":
				auto tok = parseTokens(args[1..$].join(" "));
				auto benchExp = parseMathExpression(tok);
				num = calculate(benchExp, gConstants);
				writefln("  Benchmarking... (Result = %s)", num);
				StopWatch sw;
				sw.start();
				for(int i = 0; i < 10; i++)
					calculate(benchExp, gConstants);
				sw.stop();
				int iterations = 10000;
				if(sw.peek().usecs / 10 < 300)
					iterations = 100000;
				if(sw.peek().usecs / 10 > 10000)
					iterations = 1000;
				if(sw.peek().usecs / 10 > 100000)
					iterations = 100;
				writefln("  Doing %s iterations", iterations);
				sw.reset();
				sw.start();
				for(int i = 0; i < iterations; i++)
					calculate(benchExp, gConstants);
				sw.stop();
				writefln("  Took %sµs on average", sw.peek().usecs / cast(float)iterations);
				break;
			case "dofile":
				string file = args[1..$].join(" ").strip();
				if(!std.file.exists(file)) {
					writeln(file, " does not exist!");
					break;
				}
				if(std.file.exists(file ~ ".out")) {
					writeln(file, ".out already exists! Replace? [y/N]");
					string answer = readln().toLower().strip();
					if(answer != "y" && answer != "yes")
						break;
				}
				int lineN = 0;
				try {
					string[] lines = (cast(string)std.file.readText(file)).split("\n");
					string output = "";
					foreach(line; lines) {
						lineN++;
						Number result;
						if(parseExpression(result, line.strip(), false)) {
							output ~= line.strip() ~ " = " ~ result.toString() ~ "\n";
						}
					}
					std.file.write(file ~ ".out", output);
				} catch(SyntaxException e) {
					writeln(e, " in line ", lineN, " in file ", file);
				} catch(Exception e) {
					writeln(e);
				}
				writeln("Written to ", file, ".out");
				break;
			case "Kappa":
				writeln("    ▄▀▀▀▀▀░▀▄▄▄▄
  ▄▀▓▒▓▒▒▓▒▓▓▒▓▒▀▄
▄▀▓▓▒▓▒▓▓▒▓▒▓▒▒▓▓▒░
░▒▓▒▓▒▓▒▒▒      ▒▒░
░▒▒▒▒▒▓▒▓        ▒░
▒▒▒▒▒▓            ░
▒▒▒▒    ▄▄▄▄   ▄▄▄▀
 ▀▄▒   ▀▓▓▒▒  ▓▒░
▀▄            ▀▄  ░
 ▀ ▀     ▄▄▄▄▄▄   ░
  ▀      ▀▄▄▄▄▄▀  ░
   ▀▄▄░░    ▀▀ ░▄▀
     ▀░▄░░    ░▄▀
        ▀▀░▄▄▄▄▀
Kappa");
				break;
			case "solve":
				auto arg = args[1..$].join(" ");
				auto lhs = parseTokens(arg.split("=")[0]);
				auto rhs = parseTokens(arg.split("=")[1]);
				auto lhsExp = parseMathExpression(lhs);
				auto rhsExp = parseMathExpression(rhs);

				static if(DefaultBitSize >= 64) {
					Number max = 1;
					max <<= DefaultBitSize - 2;
					Number[string] constants = gConstants;
					Number result;

					for(Number i = 0; i < max; i++)
					{
						constants["X"] = i;
						if((result = calculate(lhsExp, constants)) == calculate(rhsExp, constants)) {
							writeln(" x = ", i);
							break CommandLoop;
						}

						constants["X"] = -i;
						if((result = calculate(lhsExp, constants)) == calculate(rhsExp, constants)) {
							writeln(" x = ", -i);
							break CommandLoop;
						}
					}
					writeln("Not found");
				} else {
					long max = 1L << (DefaultBitSize - 2);
					Number[string] constants = gConstants;
					Number result;

					for(long i = 0; i < max; i++)
					{
						constants["X"] = Number(i);
						if((result = calculate(lhsExp, constants)) == calculate(rhsExp, constants)) {
							writeln(" x = ", i);
							break CommandLoop;
						}

						constants["X"] = -constants["X"];
						if((result = calculate(lhsExp, constants)) == calculate(rhsExp, constants)) {
							writeln(" x = ", -i);
							break CommandLoop;
						}
					}
					writeln("Not found");
				}
				break;
			case "vars":
				while(true) {
					writeln("Enter variable name to edit or '$' to exit");
					string input = readln().strip().toUpper();
					if(input == "$")
						break;
					auto match = input.matchFirst(identifier);
					if(match.hit.length != input.length) {
						writeln("Invalid variable name!");
						writeln();
						continue;
					}
					writef("Enter value for '%s': ", input);
					auto tok = parseTokens(readln().strip());
					gConstants[input] = calculate(parseMathExpression(tok), gConstants);
					writefln("Set '%s' to %s", input, gConstants[input]);
					writeln();
				}
				break;
			default:
				writeln("Unknown Command. Type 'help' or type an expression.");
				break;
		}
		return false;
	}
	auto tokens = parseTokens(expr);
	if(tokens.length == 0)
		return false;
	LinearExpression[] expressions;
	if(tokens[0].type == TokenType.Equals) {
		tokens = tokens[1 .. $];
	}
	expressions = parseMathExpression(tokens);
	num = calculate(expressions, gConstants);
	return true;
}

Number[string] gConstants;

void main(string[] args) {
	version(unittest)
		return;
	else {
		std.file.write("log.txt", "");
		writefln("Binary Calculator (%s bit)", DefaultBitSize);
		writeln("Enter a command or any expression with an optional leading '=' (equals sign)");
		StopWatch sw;
		if(args.length > 1) {
			foreach(file; args[1 .. $]) {
				Number trash;
				parseExpression(trash, "dofile " ~ file);
			}
		}
		while(true) {
			write("> ");
			string input = readln();
			try {
				gConstants["RNDB"] = Number(uniform(0, 2));
				gConstants["RND"] = Number(uniform(0, 32768));

				sw.reset();
				sw.start();
				Number result;
				if(parseExpression(result, input)) {
					gConstants["ANS"] = result;
					sw.stop();
					char[] binary = new char[result.value.length];
					int i = 0;
					foreach_reverse(bit; result.value)
						binary[i++] = bit == 0 ? '0' : '1';
					writefln("= %s\n= 0b%s\n  (Took %sµs)", result, binary, sw.peek().usecs);
				}
			} catch(SyntaxException e) {
				auto spaces = new char[e.position + 1];
				spaces[] = ' ';
				writeln(spaces, "^ here");
				writeln(e);
				std.file.append("log.txt", to!string(e) ~ "\n");
			} catch(Exception e) {
				writeln(e);
				std.file.append("log.txt", to!string(e) ~ "\n");
			} catch(AssertError e) {
				writeln(e.msg);
				std.file.append("log.txt", to!string(e) ~ "\n");
			}
		}
	}
}
