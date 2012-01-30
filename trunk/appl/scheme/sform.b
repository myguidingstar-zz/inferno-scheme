implement SForm;

include "sys.m";
include "draw.m";

include "bufio.m";
bufio: Bufio;
Iobuf: import bufio;

include "cell.m";
cell: SCell;
Cell: import cell;
Pair: import cell;
Env: import cell;

include "scheme.m";
scheme: Scheme;
eval: import scheme;

include "sform.m";

stdout:  ref Iobuf = nil;
lsys: Sys;

init(sys: Sys, sch: Scheme, c: SCell)
{
	cell = c;
	scheme = sch;
bufio = load Bufio Bufio->PATH;

	e := cell->envstack;
	e = ref Env("alt", cell->SpecialForm, nil, lalt) :: e;
	e = ref Env("quote", cell->SpecialForm, nil, quote) :: e;
	e = ref Env("quasiquote", cell->SpecialForm, nil, qquote) :: e;
	e = ref Env("define", cell->SpecialForm, nil, define) :: e;
	e = ref Env("delay", cell->SpecialForm, nil, delay) :: e;
	e = ref Env("force", cell->SpecialForm, nil, force) :: e;
	e = ref Env("if", cell->SpecialForm, nil, ifsf) :: e;
	e = ref Env("lambda", cell->SpecialForm, nil, lambda) :: e;
	e = ref Env("set!", cell->SpecialForm, nil, setbang) :: e;
	e = ref Env("unquote", cell->SpecialForm, nil, unquote) :: e;
	e = ref Env("unquote-splicing", cell->SpecialForm, nil, unquotesplice) :: e;
	e = ref Env("and", cell->SpecialForm, nil, land) :: e;
	e = ref Env("begin", cell->SpecialForm, nil, begin) :: e;
	e = ref Env("or", cell->SpecialForm, nil, lor) :: e;
	e = ref Env("case", cell->SpecialForm, nil, lcase) :: e;
	e = ref Env("cond", cell->SpecialForm, nil, cond) :: e;
	e = ref Env("do", cell->SpecialForm, nil, ldo) :: e;
	e = ref Env("let", cell->SpecialForm, nil, let) :: e;
	e = ref Env("let*", cell->SpecialForm, nil, letstar) :: e;
	e = ref Env("letrec", cell->SpecialForm, nil, letrec) :: e;
	e = ref Env("spawn", cell->SpecialForm, nil, lspawn) :: e;
	cell->envstack = e;
	l := e;
	while(l != nil) {
		x := hd l;
		if(x.ilk == cell->BuiltIn || x.ilk == cell->SpecialForm)
			x.val = ref Cell.Symbol(x.name, x);
		l = tl l;
	}
lsys = sys;
stdout = bufio->fopen(sys->fildes(1), Bufio->OWRITE);
}

lalt(args: ref Cell): (int, ref Cell)
{
	x := args;
	i := 0;
	while(x != nil && !cell->isnil(x)) {
		++i;
		x = cell->lcdr(x);
	}
	ca := array[i] of chan of ref Cell;
	x = args;
	i = 0;
	while(x != nil && !cell->isnil(x)) {
		y := cell->lcar(x);
		if (y != nil && !cell->isnil(y)) {
			pick z := eval(y) {
			Channel =>
				ca[i++] = z.ch;
			}
		}
		x = cell->lcdr(x);
	}
	(idx, val) := <- ca;
	ic := ref Cell.Number(big idx, big 1, real idx, cell->Integer|cell->Exact);
	return (0, cell->lcons(ic, cell->lcons(val, ref Cell.Link(nil))));
}

land(args: ref Cell): (int, ref Cell)
{
	c: ref Cell;

	c = ref Cell.Boolean(1);
	p := cell->lcar(args);
	if (p == nil || cell->isnil(p))
		return(0, ref Cell.Boolean(1));
	l := cell->lcdr(args);
	while(l != nil && !(cell->isnil(l))) {
		c = eval(p);
		pick cn := c {
		Boolean =>
			if(cn.b == 0)
				return (0, c);
		}
		if(l == nil || cell->isnil(l))
			break;
		p = cell->lcar(l);
		l = cell->lcdr(l);
	}
	return (1, ref Cell.Continuation(p, cell->envstack));
}

begin(args: ref Cell): (int, ref Cell)
{
	c: ref Cell;

	p := cell->lcar(args);
	if(p == nil) {
		cell->error("wrong number of arguments in begin\n");
		return (0, nil);
	}
	l := cell->lcdr(args);
	while(l != nil && !(cell->isnil(l))) {
		c = eval(p);
		p = cell->lcar(l);
		l = cell->lcdr(l);
	}
	return (1, ref Cell.Continuation(p, cell->envstack));
}

lbegin(args: ref Cell): (int, ref Cell)
{
	(t, x) := begin(args);
	if(t)
		return (0, eval(x));
	else
		return (0, x);
}

ldo(args: ref Cell): (int, ref Cell)
{
	r: ref Cell;
	t: int;

	oenv := cell->envstack;
	il := cell->lcar(args);
	tc := cell->lcdr(args);
	te := cell->lcar(tc);
	c := cell->lcdr(tc);
	ii := il;
	el := oenv;
	while(ii != nil && !cell->isnil(ii)) {
		ij := cell->lcar(ii);
		pick x := cell->lcar(ij) {
		Symbol =>
			(nil, el) = cell->ldefine(x.sym, eval(cell->lcar(cell->lcdr(ij))), el);
		}
		ii = cell->lcdr(ii);
	}
	cell->envstack = el;
bigloop:
	while(1) {
		tv := eval(cell->lcar(te));
		if(tv == nil || cell->isnil(tv)) {
			(nil, r) = lbegin(cell->lcdr(te));
			break;
		}
		pick y := tv {
		Boolean =>
			if (y.b == 1) {
				(t, r) = begin(cell->lcdr(te));
				break bigloop;
			}
		}
		if(c != nil && !cell->isnil(c))
			lbegin(c);

		ii = il;
		el = oenv;
		while(ii != nil && !cell->isnil(ii)) {
			ij := cell->lcar(ii);
			pick x := cell->lcar(ij) {
			Symbol =>
				upd := cell->lcar(cell->lcdr(cell->lcdr(ij)));
				if (upd == nil || cell->isnil(upd))
					(nil, el) = cell->ldefine(x.sym, eval(upd), cell->envstack);
				else
					(nil, el) = cell->ldefine(x.sym, eval(upd), el);
			}
			ii = cell->lcdr(ii);
		}
		cell->envstack = el;
	}
	if (t == 0)
		return (0, r);
	pick cont := r {
	Continuation =>
		res := ref Cell.Continuation(cont.exp, cell->envstack);
		cell->envstack = oenv;
		return (1, res);
	* =>
		cell->envstack = oenv;
		return (0, r);
	}
}

lcase(args: ref Cell): (int, ref Cell)
{
	x := cell->lcar(args);
	l := cell->lcdr(args);
	if(x == nil || l == nil || cell->isnil(l)) {
		cell->error("wrong number of expressions in case\n");
		return (0, nil);
	}
	key := eval(cell->lcar(args));
	if(key == nil) {
		cell->error("key expression missing in case\n");
		return (0, nil);
	}
	do {
		clause := cell->lcar(l);
		if(clause == nil || cell->isnil(clause)) {
			cell->error("non-pair clause in case\n");
			return (0, nil);
		}
		data := cell->lcar(clause);
		if(data == nil || cell->isnil(data)) {
			cell->error("non-pair clause in case\n");
			return (0, nil);
		}
		exprs := cell->lcdr(clause);
		if(exprs == nil || cell->isnil(exprs)) {
			cell->error("non-pair clause in case\n");
			return (0, nil);
		}
		pick elp := data {
		Symbol =>
			if(elp.sym == "else")
				return begin(exprs);
		}
		dl := data;
		do {
			datum := cell->lcar(dl);
			if(cell->leqvp(key, datum) == 1)
				return begin(exprs);
			dl = cell->lcdr(dl);
		} while(dl != nil && !(cell->isnil(dl)));
		l = cell->lcdr(l);
	} while(l != nil && !(cell->isnil(l)));
	return (0, nil);
}

procel(res, el: ref Cell): (int, ref Cell)
{
	if(el == nil || cell->isnil(el))
		return (0, res);
	pick arrow := cell->lcar(el) {
	Symbol =>
		if(arrow.sym == "=>") {
			l := cell->lcdr(el);
			if(l == nil || cell->isnil(l))
				return (0, nil);
			c := eval(cell->lcar(l));
			qr := cell->lcons(ref Cell.Symbol("quote", nil),
				cell->lcons(res, ref Cell.Link(nil)));
			return (0, eval(cell->lcons(c, cell->lcons(qr, ref Cell.Link(nil)))));
		}
	}
	return begin(el);
}

cond(args: ref Cell): (int, ref Cell)
{
	cl := cell->lcar(args);
	l := cell->lcdr(args);
	if(cl == nil || cell->isnil(cl) || l == nil || cell->isnil(l)) {
		cell->error("wrong number of arguments in cond\n");
		return (0, nil);
	}
	while(1) {
		test := cell->lcar(cl);
		if(test == nil || cell->isnil(test)) {
			cell->error("invalid test in cond\n");
			return (0, nil);
		}
		res := eval(test);
		if (res == nil || cell->isnil(res)) {
			cell->error("invalid cond expression\n");
			return (0, nil);
		}
		el := cell->lcdr(cl);
		pick r := res {
		Boolean =>
			if(r.b == 1)
				return procel(res, el);
		* =>
			return procel(res, el);
		}
		if(l == nil || cell->isnil(l))
			break;
		cl = cell->lcar(l);
		l = cell->lcdr(l);
	}
	return (0, nil);
}

define(args: ref Cell): (int, ref Cell)
{
	x := cell->lcar(args);
	l := cell->lcdr(args);
	if(x == nil || l == nil) {
		cell->error("wrong number of arguments in define\n");
		return (0, nil);
	}
	pick y := x {
	Symbol =>
		e := cell->lookupsym(y.sym);
		if(e != nil) {
			e.val = eval(cell->lcar(l));
			return (0, ref Cell.Symbol(y.sym, e));
		}
		(c, el) := cell->ldefine(y.sym, eval(cell->lcar(l)), cell->globalenv);
		cell->globalenv = el;
		return (0, c);
	Link =>
		pick z := cell->lcar(x) {
		Symbol =>
			lc := ref Cell.Symbol("lambda", cell->lookupsym("lambda"));
			fp := ref Cell.Link(ref Pair(cell->lcdr(x), l));
			lp := ref Cell.Link(ref Pair(lc, fp));
			e := cell->lookupsym(z.sym);
			if(e != nil) {
				e.val = eval(lp);
				return (0, ref Cell.Symbol(z.sym, e));
			}
			(c, el) := cell->ldefine(z.sym, eval(lp), cell->globalenv);
			cell->globalenv = el;
			return (0, c);
		}
	}
	return (0, ref Cell.Link(nil));
}

delay(args: ref Cell): (int, ref Cell)
{
	return (0, ref Cell.Promise(cell->lcar(args), nil, cell->envstack));
}

force(args: ref Cell): (int, ref Cell)
{
	p := eval(cell->lcar(args));
	pick x := p {
	Promise =>
		oenv := cell->envstack;
		cell->envstack = x.env;
		if (x.val == nil)
			x.val = eval(x.proc);
		cell->envstack = oenv;
		return (0, x.val);
	}
	return (0, p);
}

ifsf(args: ref Cell): (int, ref Cell)
{
	e3: ref Cell;

	e1 := cell->lcar(args);
	l := cell->lcdr(args);
	e2 := cell->lcar(l);
	if(e1 == nil || e2 == nil || l == nil) {
		cell->error("wrong number of expressions in if\n");
		return (0, nil);
	}
	l = cell->lcdr(l);
	if(l == nil || cell->isnil(l))
		e3 = ref Cell.Link(nil);
	else
		e3 = cell->lcar(l);
	truth := eval(e1);
	pick x := truth {
	Boolean =>
		if(x.b == 0)
			return (1, ref Cell.Continuation(e3, cell->envstack));
	}
	return (1, ref Cell.Continuation(e2, cell->envstack));
}

lambda(args: ref Cell): (int, ref Cell)
{
	if(args == nil) {
		cell->error("too few arguments in lambda expressions\n");
		return (0, nil);
	}
	pick x := args {
	Link =>
		if(x.next == nil || x.next.cdr == nil)
			return (0, ref Cell.Link(nil));
		return (0, ref Cell.Lambda(x.next.car,
			x.next.cdr, cell->envstack));
	}
	cell->error("invalid lambda expression\n");
	return (0, nil);	
}

let(args: ref Cell): (int, ref Cell)
{
	vals: list of (string, ref Cell);

	if(args == nil || cell->isnil(args)) {
		cell->error("too few arguments in let\n");
		return (0, nil);
	}
	binds := cell->lcar(args);
	exprs := cell->lcdr(args);
	if(binds == nil || cell->isnil(binds))
		return begin(exprs);
	func_name := "";
	pick x := binds {
	Symbol =>
		func_name = x.sym;
		binds = cell->lcar(exprs);
		exprs = cell->lcdr(exprs);
	}
	vals = nil;
	bl := binds;
	do {
		b := cell->lcar(bl);
		if(b == nil || cell->isnil(b))
			break;
		exp := cell->lcdr(b);
		pick var := cell->lcar(b) {
		Symbol =>
			(nil, y) := lbegin(exp);
			vals = (var.sym, y) :: vals;
		}
		bl = cell->lcdr(bl);
	} while(bl != nil && !(cell->isnil(bl)));
	saveenv := cell->envstack;
	bl = binds;
	do {
		b := cell->lcar(bl);
		if(b == nil || cell->isnil(b))
			break;
		if(vals == nil)
			break;
		(var, val) := hd vals;
		(nil, el) := cell->ldefine(var, val, cell->envstack);
		cell->envstack = el;
		bl = cell->lcdr(bl);
		vals = tl vals;
	} while(bl != nil && !(cell->isnil(bl)));
	if(func_name != "") {
		bl = binds;
		formals := ref Cell.Link(nil);
		f: ref Cell;
		f = formals;
		do {
			fname: string;
			b := cell->lcar(bl);
			if(b == nil || cell->isnil(b))
				break;
			pick bn := cell->lcar(b) {
			Symbol =>
				fname = bn.sym;
			}
			pick fl := f {
			Link =>
				fl.next = ref Pair(
					ref Cell.Symbol(fname, nil), ref Cell.Link(nil));
				f = cell->lcdr(f);
			}
			bl = cell->lcdr(bl);
		} while(bl != nil && !(cell->isnil(bl)));
		lambda_exp := cell->lcons(
			ref Cell.Symbol("lambda", cell->lookupsym("lambda")),
				cell->lcons(formals,
				cell->lcons(cell->lcar(exprs), ref Cell.Link(nil))));
		(nil, el) := cell->ldefine(
			func_name, eval(lambda_exp), cell->envstack);
		cell->envstack = el;
	}
	#res := lbegin(exprs);
	(t, r) := begin(exprs);
	if (t == 0)
		return (0, r);
	pick c := r {
	Continuation =>
		res := ref Cell.Continuation(c.exp, cell->envstack);
		cell->envstack = saveenv;
		return (1, res);
	* =>
		cell->envstack = saveenv;
		return (0, r);
	}
}

letstar(args: ref Cell): (int, ref Cell)
{
	if(args == nil || cell->isnil(args)) {
		cell->error("too few arguments to let*\n");
		return (0, nil);
	}
	binds := cell->lcar(args);
	exprs := cell->lcdr(args);
	if(binds == nil || cell->isnil(binds))
		return begin(exprs);
	saveenv := cell->envstack;
	bl := binds;
	do {
		b := cell->lcar(bl);
		if(b == nil || cell->isnil(b))
			break;
		pick var := cell->lcar(b) {
		Symbol =>
			exp := cell->lcdr(b);
			(nil, y) := lbegin(exp);
			(nil, el) := cell->ldefine(var.sym, y, cell->envstack);
			cell->envstack = el;
		}
		bl = cell->lcdr(bl);
	} while(bl != nil && !(cell->isnil(bl)));
	#res := lbegin(exprs);
	(t, r) := begin(exprs);
	if (t == 0)
		return (0, r);
	pick c := r {
	Continuation =>
		res := ref Cell.Continuation(c.exp, cell->envstack);
		cell->envstack = saveenv;
		return (1, res);
	* =>
		cell->envstack = saveenv;
		return (0, r);
	}
}

letrec(args: ref Cell): (int, ref Cell)
{
	return letstar(args);
}

lor(args: ref Cell): (int, ref Cell)
{
	c: ref Cell;

	if(args == nil)
		return (0, nil);
	if(cell->isnil(args))
		return (0, ref Cell.Boolean(0));
	p := cell->lcar(args);
	if (p == nil || cell->isnil(p))
		return (0, ref Cell.Boolean(0));
	l := cell->lcdr(args);
	while(l != nil && !(cell->isnil(l))) {
		c = eval(p);
		pick cn := c {
		Boolean =>
			if(cn.b == 1)
				return (0, c);
		* =>
			return (0, c);
		}
		p = cell->lcar(l);
		l = cell->lcdr(l);
	}
	return (1, ref Cell.Continuation(p, cell->envstack));
}

lqquote(expr: ref Cell, level: int): (int, ref Cell)
{
	if(expr == nil || cell->isnil(expr))
		return (0, expr);
	pick y := expr {
	Link =>
		if(y.next == nil || y.next.car == nil)
			return (0, expr);
		pick z := y.next.car {
		Symbol =>
			if(z.sym == "unquote") {
				if(level == 1) {
					(nil, q) := unquote(y.next.cdr);
					return (0, q);
				}
				else {
					(nil, c) := lqquote(y.next.cdr, level - 1);
					return (0, ref Cell.Link(ref Pair(z, c)));
				}
			}
			if(z.sym == "unquote-splicing") {
				if(level == 1) {
					(nil, q) := unquote(y.next.cdr);
					return (1, q);
				}
				else {
					(nil, c) := lqquote(y.next.cdr, level - 1);
					return (0, ref Cell.Link(ref Pair(z, c)));
				}
			}
			if(z.sym == "quasiquote") {
				(nil, c) := lqquote(y.next.cdr, level + 1);
				return (0, ref Cell.Link(ref Pair(z, c)));
			}
		}
		(n, ca) := lqquote(y.next.car, level);
		(nil, cd) := lqquote(y.next.cdr, level);
		if(n == 1)
			return (0, cell->lappend(ca, cd));
		else
			return (0, ref Cell.Link(ref Pair(ca, cd)));
	Vector =>
		n := len y.v;
		nl: list of ref Cell;
		nl = nil;
		for(i := 0; i < n; ++i) {
			(qqs, c) := lqquote(y.v[i], level);
			if(qqs == 0) {
				nl = c :: nl;
			}
			else {
				p := c;
				while(1) {
					if(p == nil || cell->isnil(p))
						break;
					nl = cell->lcar(p) :: nl;
					p = cell->lcdr(p);
				}
			}
		}
		nv := array[len nl] of ref Cell;
		for(i = len nl - 1; i >= 0; --i) {
			nv[i] = hd nl;
			nl = tl nl;
		}
		return (0, ref Cell.Vector(nv));
	* =>
		return (0, expr);
	}
}

qquote(args: ref Cell): (int, ref Cell)
{
	if(args == nil || cell->isnil(args)) {
		cell->error("wrong number of arguments to quasiquote\n");
		return (0, nil);
	}
	(nil, c) := lqquote(cell->lcar(args), 1);
	return (0, c);
}

quote(args: ref Cell): (int, ref Cell)
{
	if(args == nil || cell->isnil(args))
		return (0, nil);
	return (0, cell->lcar(args));
}

setbang(args: ref Cell): (int, ref Cell)
{
	if(args == nil || cell->isnil(args))
		return (0, nil);
	p := cell->lcar(args);
	if(p == nil || cell->isnil(p))
		return (0, nil);
	l := cell->lcdr(args);
	if(l == nil || cell->isnil(l))
		return (0, nil);
	pick y := p {
	Symbol =>
		e := cell->lookupsym(y.sym);
		if(e == nil) {
			cell->error("Cannot set unbound variable\n");
			return (0, nil);
		}
		e.val = eval(cell->lcar(l));
	}
	return (0, p);
}

seval(args: ref Cell)
{
	if (args == nil || cell->isnil(args)) {
		cell->error("Empty spawn");
		exit;
	}
	eval(cell->lcar(args));
	exit;
}

lspawn(args: ref Cell): (int, ref Cell)
{
	spawn seval(args);
	return (0, ref Cell.Link(nil));
}

unquote(args: ref Cell): (int, ref Cell)
{
	x := cell->lcar(args);
	if(x == nil) {
		cell->error("wrong number of arguments to unquote\n");
		return (0, nil);
	}
	return (0, eval(x));
}

unquotesplice(args: ref Cell): (int, ref Cell)
{
	x := cell->lcar(args);
	if(x == nil) {
		cell->error("wrong number of arguments to unquote-splicing\n");
		return (0, nil);
	}
	c := eval(x);
	if(c == nil || cell->isnil(c)) {
		cell->error("invalid expression in unquote-splicing\n");
		return (0, nil);
	}
	pick y := c {
	Link =>
		return (0, y.next.car);
	* =>
		cell->error("invalid expression in unquote-splicing\n");
	}
	return (0, nil);
}

