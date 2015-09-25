module number;
import std.algorithm : min;
import std.string : munch;

enum DefaultBitSize = 128;

enum NumberType : ubyte {
	bin = 2, dec = 10, hex = 16
}

alias Number = NumberImpl!(DefaultBitSize);

struct NumberImpl(int BitSize) {
	enum DecSize = BitSize / 2;
	alias num_t = ubyte[BitSize];

	num_t value;

	this(in num_t value) {
		this.value = value;
		assert(valid);
	}

	this(in long value) {
		num_t generated;
		for(long i = min(BitSize - 1, 63); i >= 0; i--) {
			generated[i] = value >> i & 1;
		}
		this.value = generated;
		assert(valid);
	}

	this(in int value) {
		num_t generated;
		for(int i = min(BitSize - 1, 31); i >= 0; i--) {
			generated[i] = value >> i & 1;
		}
		this.value = generated;
		assert(valid);
	}

	this(int Bits)(in NumberImpl!Bits value) {
		static if(Bits == BitSize)
			this.value = value.value;
		else static if(Bits > BitSize) {
			this.value[0 .. $ - 1] = value.value[0 .. BitSize - 1];
		} else {
			if(value.isNegative)
				this.value[] = 1;
			this.value[0 .. Bits - 1] = value.value[0 .. $ - 1];
		}
		assert(valid);
	}

	this(string value) {
		NumberType numberType = NumberType.dec;
		assert(value.length > 0);
		bool negative = false;
		if(value[0] == '+') value = value[1 .. $];
		if(value[0] == '-') {
			negative = true;
			value = value[1 .. $];
		}
		if(value.length > 2) {
			if(value[0 .. 2] == "0x") {
				numberType = NumberType.hex;
				value = value[2 .. $];
			} else if(value[0 .. 2] == "0b") {
				numberType = NumberType.bin;
				value = value[2 .. $];
			}
		}
		char[] reversed = new char[value.length];
		for(int i = 0; i < reversed.length; i++)
			reversed[i] = value[$ - i - 1];
		value = reversed.idup;
		int pos = 0;
		while(value.length > 0) {
			ubyte ch = value[0];
			ubyte realValue;
			switch(ch) {
				case '0': .. case '9':
					realValue = cast(ubyte)(ch - cast(ubyte)'0');
					if(realValue > 1)
						assert(numberType >= NumberType.dec, "Unexpected numeric literal (remove 0b, or");
					break;
				case 'a': .. case 'f':
					ch = cast(ubyte)(ch - cast(ubyte)'a' + cast(ubyte)'A');
					goto case;
				case 'A': .. case 'F':
					assert(numberType >= NumberType.hex, "Unexpected numeric literal (prepend 0x)");
					realValue = cast(ubyte)(10 + ch - cast(ubyte)'A');
					break;
				default:
					assert(0, "Unexpected numeric literal");
			}
			NumberImpl!BitSize num = NumberImpl!BitSize(cast(int)numberType);
			num = num.pow(NumberImpl!BitSize(cast(int)pos));
			num *= NumberImpl!BitSize(cast(int)realValue);
			this += num;
			pos++;
			value = value[1 .. $];
		}
	}

	NumberImpl!BitSize add(NumberImpl!BitSize other) const {
		num_t raw = value[];
		bool overflow = false;
		for(int i = 0; i < BitSize; i++) {
			if(raw[i] != 0 && other[i] && overflow != 0) {
				raw[i] = true; // 1+1+1 = 11
				overflow = true;
			} else if((raw[i] != 0 && other[i]) || (raw[i] != 0 && overflow != 0) || (other[i] && overflow != 0)) {
				raw[i] = false; // 1+1 = 10
				overflow = true;
			} else if(raw[i] != 0 || other[i] || overflow != 0) {
				raw[i] = true; // 1 = 1
				overflow = false;
			}
		}
		return NumberImpl!BitSize(raw);
	}

	NumberImpl!BitSize sub(NumberImpl!BitSize other) const {
		return add(-other);
	}

	NumberImpl!BitSize udivide(NumberImpl!BitSize other) const {
		assert(other != 0, "Division by Zero");
		if(other > this)
			return NumberImpl!BitSize(0);
		NumberImpl!BitSize quotient = 0;
		NumberImpl!BitSize remainder = 0;
		for(int i = BitSize - 1; i >= 0; i--) {
			remainder <<= 1;
			remainder[0] = this[i];
			if(remainder >= other) {
				remainder -= other;
				quotient[i] = 1;
			}
		}
		return quotient;
	}

	private NumberImpl!BitSize moddiv(NumberImpl!BitSize other) {
		assert(other != 0, "Division by Zero");
		if(other > this) {
			auto oldVal = this.value;
			this.value[] = 0;
			return Number(oldVal);
		}
		NumberImpl!BitSize quotient = 0;
		NumberImpl!BitSize remainder = 0;
		for(int i = BitSize - 1; i >= 0; i--) {
			remainder <<= 1;
			remainder[0] = this[i];
			if(remainder >= other) {
				remainder -= other;
				quotient[i] = 1;
			}
		}
		this.value = quotient.value;
		return remainder;
	}

	NumberImpl!BitSize divide(NumberImpl!BitSize other) const {
		if(other.isNegative && isNegative) {
			return negate.udivide(other.negate);
		} else if(other.isNegative) {
			return udivide(other.negate).negate;
		} else if(isNegative) {
			return negate.udivide(other).negate;
		} else {
			return udivide(other);
		}
	}

	NumberImpl!BitSize mul(NumberImpl!BitSize other) const {
		NumberImpl!BitSize result = 0;
		NumberImpl!BitSize base = this;
		while(other) {
			if(other & 1)
				result += base;
			base <<= 1;
			other >>>= 1;
		}
		return result;
	}

	NumberImpl!BitSize pow(NumberImpl!BitSize other) const {
		NumberImpl!BitSize result = 1;
		NumberImpl!BitSize base = this;
		while(other) {
			if(other & 1)
				result *= base;
			other >>>= 1;
			base *= base;
		}
		return result;
	}

	NumberImpl!BitSize modulo(NumberImpl!BitSize other) const {
		NumberImpl!BitSize clone = NumberImpl!BitSize(value);
		while(clone >= other)
			clone -= other;
		return clone;
	}

	NumberImpl!BitSize bsl(NumberImpl!BitSize other) const {
		if(other > BitSize)
			return NumberImpl!BitSize(0);
		NumberImpl!BitSize clone = value;
		while(other > 0) {
			for(int i = BitSize - 2; i >= 1; i--) { // Start after sign, stop one before
				*(clone.value.ptr + i) = *(clone.value.ptr + i - 1);
			}
			clone.value[0] = 0; // Fill last
			other--;
		}
		return clone;
	}

	NumberImpl!BitSize bsr(NumberImpl!BitSize other) const {
		if(other > BitSize)
			return NumberImpl!BitSize(0);
		NumberImpl!BitSize clone = value;
		while(other > 0) {
			for(int i = 0; i < BitSize - 2; i++) { // End 2 after sign
				*(clone.value.ptr + i) = *(clone.value.ptr + i + 1);
			}
			clone.value[BitSize - 2] = 0; // Fill first after sign
			other--;
		}
		return clone;
	}

	NumberImpl!BitSize ubsr(NumberImpl!BitSize other) const {
		if(other > BitSize)
			return NumberImpl!BitSize(0);
		NumberImpl!BitSize clone = value;
		while(other > 0) {
			for(int i = 0; i < BitSize - 1; i++) { // End 1 after sign
				*(clone.value.ptr + i) = *(clone.value.ptr + i + 1);
			}
			clone.value[BitSize - 1] = 0; // Set sign to 0
			other--;
		}
		return clone;
	}

	NumberImpl!BitSize and(NumberImpl!BitSize other) const {
		NumberImpl!BitSize clone = value;
		for(int i = 0; i < BitSize; i++)
			clone[i] &= other[i];
		return clone;
	}

	NumberImpl!BitSize or(NumberImpl!BitSize other) const {
		NumberImpl!BitSize clone = value;
		for(int i = 0; i < BitSize; i++)
			clone[i] |= other[i];
		return clone;
	}

	NumberImpl!BitSize xor(NumberImpl!BitSize other) const {
		NumberImpl!BitSize clone = value;
		for(int i = 0; i < BitSize; i++)
			clone[i] ^= other[i];
		return clone;
	}

	bool valid() @property const {
		for(int i = 0; i < BitSize; i++)
			if(value[i] != 0 && value[i] != 1)
				return false;
		return true;
	}

	T opCast(T)() const {
		static if(is(T == bool))
			return this != 0;
		else static if(is(T == int))
			return this.toSmallNumber;
	}

	bool opIndex(size_t i) const {
		assert(value[i] == 0 || value[i] == 1, "Malformed binary representation");
		return value[i] != 0;
	}

	void opIndexAssign(int val, size_t i) {
		value[i] = cast(ubyte)(val != 0 ? 1 : 0);
	}

	auto opIndexOpAssign(string op)(int b, size_t i) {
		return mixin("value[i] " ~ op ~ "= b");
	}

	char toDecChar() @property const {
		assert(this < 10 && this >= 0);
		for(int i = 0; i < 10; i++) {
			if(this == i)
				return cast(char)(i + '0');
		}
		assert(0);
	}

static if(BitSize < 64)
	long toSmallNumber() @property const nothrow @safe {
		long num;
		for(long i = 0; i < BitSize - 1; i++) {
			num |= cast(long)value[i] << i;
		}
		if(value[BitSize - 1] != 0)
			num = -((2L << (BitSize - 2)) - num); // Create correct negative value
		return num;
	}

	string toString() @property const {
		string sign = "";
		Number value = this;
		if(isNegative) {
			sign = "-";
			value = -value;
		}
		string num = "";
		Number remainder;
		while(value) {
			num = (value.moddiv(Number(10)).toDecChar) ~ num;
		}
		num = sign ~ num;
		return num;
	}

	bool isPositive() @property const {
		return value[BitSize - 1] != 0;
	}

	bool isNegative() @property const {
		return value[BitSize - 1] == 1;
	}

	int opCmp(T)(T b) const {
		NumberImpl!BitSize num = NumberImpl!BitSize(b);
		if(value == num.value)
			return 0;
		return (this - num).isPositive ? -1 : 1;
	}

	bool opEquals(int b) const {
		return value == NumberImpl!BitSize(b).value;
	}

	bool opEquals(NumberImpl!BitSize b) const {
		return value == b.value;
	}

	NumberImpl!BitSize invert() const {
		num_t bits = value[];
		for(int i = 1; i < BitSize; i++)
			bits[i] = bits[i] == 0 ? 1 : 0;
		return NumberImpl!BitSize(bits);
	}

	NumberImpl!BitSize uinvert() const {
		num_t bits = value[];
		for(int i = 0; i < BitSize; i++)
			bits[i] = bits[i] == 0 ? 1 : 0;
		return NumberImpl!BitSize(bits);
	}

	NumberImpl!BitSize negate() const {
		return uinvert().add(NumberImpl!BitSize(1));
	}

	NumberImpl!BitSize opUnary(string op)() {
		static if(op == "+") return NumberImpl!BitSize(value);
		else static if(op == "-") return negate();
		else static if(op == "~") return invert();
		else static if(op == "++") return this = add(NumberImpl!BitSize(1));
		else static if(op == "--") return this = sub(NumberImpl!BitSize(1));
		else static assert(0, "Unsupported unary operator " ~ op);
	}

	NumberImpl!BitSize opBinary(string op)(int other) const {
		return opBinary!(op)(NumberImpl!BitSize(other));
	}

	NumberImpl!BitSize opBinary(string op)(NumberImpl!BitSize other) const {
		static if(op == "+") return add(other);
		else static if(op == "-") return sub(other);
		else static if(op == "*") return mul(other);
		else static if(op == "/") return divide(other);
		else static if(op == "%") return modulo(other);
		else static if(op == "&") return and(other);
		else static if(op == "|") return or(other);
		else static if(op == "^") return xor(other);
		else static if(op == "^^") return pow(other);
		else static if(op == ">>") return bsr(other);
		else static if(op == ">>>") return ubsr(other);
		else static if(op == "<<") return bsl(other);
		else static assert(0, "Unsupported binary operator " ~ op);
	}

	NumberImpl!BitSize opOpAssign(string op)(int other) {
		value = opBinary!(op)(other).value;
		return this;
	}

	NumberImpl!BitSize opOpAssign(string op)(NumberImpl!BitSize other) {
		value = opBinary!(op)(other).value;
		return this;
	}
}

unittest {
	const Number num1 = 42;
	const Number num2 = 18;

	assert(num1 > num2);
	assert((num1 + num2).toString == "60");
}

unittest {
	const Number num1 = 48;
	const Number num2 = 28;

	assert(num1 > num2);
	assert((num1 - num2).toString == "20");
}

unittest {
	const Number num1 = 5;
	const Number num2 = 10;

	assert(num1 < num2);
	assert((num1 - num2).toString == "-5");
}

unittest {
	const Number num1 = 13;
	const Number num2 = 3;

	assert((num1 / num2).toString == "4");
	assert((num1 % num2).toString == "1");
}

unittest {
	const Number num1 = 4;
	const Number num2 = 5;

	assert((num1 * num2).toString == "20");
}

unittest {
	const Number num1 = 0b1101;
	const Number num2 = 2;

	assert((num1 >> num2).toString == "3");
	assert((num1 << num2).toString == "52");
}

unittest {
	const Number num1 = 0b1101;
	const Number num2 = 0b0111;

	assert((num1 & num2).toString == "5");
	assert((num1 | num2).toString == "15");
	assert((num1 ^ num2).toString == "10");
}
