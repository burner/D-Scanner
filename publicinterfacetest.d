module mod;

void fun(int);
void fun(float);

struct Foo {
	int bar;
	int func(float f, string g);
	private string dontLook();

	struct Inner {
		int value;
		private foo;
	}
}

T temp(T)(T t, int a) {
	return t * a;
}

private double notOurConcern(string[] foo) {
	assert(foo.length);
	return foo.length;
}

private class Cls {
	int uuu;
	int functi(float f);
	private string dontLookHer();
}

interface StringInterface {
	string toString() @safe;
}

struct List(T) {
	void put(F)(F f) {}
}
