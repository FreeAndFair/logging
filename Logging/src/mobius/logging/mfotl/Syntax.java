package mobius.logging.mfotl;

//TODO add specs and docs

import java.util.HashSet;
import java.util.Hashtable;
import java.util.Set;

/*
 * Define Variables, and if it is free or not
 */
class Variable {
    private final String name;
    private boolean is_free;
    private int value;
    
    public Variable(final String _name) {
        name = _name;
        is_free = true;
    }
    
    public String getName() {
        return name;
    }
    
    public void setFree(final boolean _is_free) {
        is_free = _is_free;
    }
    
    public boolean isFree() {
        return is_free;
    }
    
    public void setValue(final int _value) {
        value = _value;
    }
    
    public int getValue() {
        return value;
    }
    

    public int evaluate(final Structure _structure) {
        value = _structure.evaluateVar(name);
        return value;
    }
}

/*
 * Predicate in logical expression
 */
class Predicator {
    private final int arity;
    private final String symbol;
    private final Variable[] var;
    
    /*
     * @ ensures _var.length == _arity;
     * @ ensures _arity > 0;
     */
    public Predicator(final String _name, final int _arity, final String[] _var) {
        symbol = _name;
        arity = _arity;
        
        var = new Variable[arity];
        for (int i = 0; i < arity; i++) {
            var[i] = new Variable(_var[i]);
        }
    }
    
    public boolean evaluate(final Structure _structure) {
        int[] temp_val = new int[arity];
        for (int i = 0; i < arity; i++) {
            temp_val[i] = var[i].evaluate(_structure);
        }
        
        return _structure.evaluateRelation(symbol, temp_val);
    }
    
    /**
     * <p>
     * return a <code>String</code> that represents the formula
     * </p>
     */
    public String toString() {
        final StringBuffer _result = new StringBuffer();
        _result.append(symbol);
        _result.append(" (" + var[0].getName());
        for (int i = 1; i < arity; i++) {
            _result.append(", " + var[i].getName());
        }
        _result.append(')');
        return _result.toString();
    }
    
    public String getSymbol() {
        return symbol;
    }
    
    public int getArity() {
        return arity;
    }
    
    /*
     * ensures i in the range of arity
     */
    /*
    public Variable getVariable(int i) {
        return var[i];
    }*/
}

class TemporalOperator extends Operator {
    //public static final Hashtable<String, String> op = new Hashtable<String, String>();

    private final Interval interval;
    
    //@ assignable interval
    public TemporalOperator(final /*@ non_null @*/ String _symbol, final int _start, final int _end) {
        super(_symbol);
        interval = new Interval(_start, _end);
    }
    
    //@ assignable interval 
    public TemporalOperator(final /*@ non_null @*/ String _symbol, final int _start) {
        super(_symbol);
        interval = new Interval(_start);
    }
    
    //@ assignable interval
    public TemporalOperator(final /*@ non_null @*/ String _symbol) {
        super(_symbol);
        interval = new Interval();
    }
    
    //@ assignable interval.starty
    public void setStart(final int _start) {
        interval.start = _start;
    }
    
    //@ assignable interval.end
    public void setEnd(final int _end) {
        interval.end = _end;
    }
    
    public void setInterval(int _start, int _end) {
        interval.start = _start;
        interval.end = _end;
    }
    
    public int getStart() {
        return interval.start;
    }
    
    public int getEnd() {
        return interval.end;
    }
    
    public boolean inRange(int testVal) {
        return interval.inRange(testVal);
    }
    
    /*
    static void initVal() {
        op.put("P", "prenext");
        op.put("N", "next");
        op.put("S", "succeed");
        op.put("U", "until");
        op.put("A", "always");
    }*/
}

class FirstOrder_Operator extends Operator {
    //public static final Hashtable<String, String> op = new Hashtable<String, String>();
    
    FirstOrder_Operator() {
        super();
    }
    
    /*
    void initVal() {
        op.put("!", "not");
        op.put("&", "and");
        
        op.put("E", "exist");
        op.put("V", "all");
        
        op.put("|", "or");
        op.put("->", "imply");
        
        
        op.put("(", "(");
        op.put(")", ")");
        op.put("[", "[");
        op.put(",", ",");
        
    }*/
}

class Operator {
    /* public static final Hashtable<String, String> OPER = new Hashtable<String, String>();*/
    private static final Set TEMP_OPER = new HashSet();
    private static final Set FIRST_OPER = new HashSet();

    public String symbol;
    private static Logger logger = new Logger();
    
    public Operator() {
        init();
    }
    
    public Operator(final /*@non-null */ String _symbol) {
        symbol = _symbol;
    }
    
    public static boolean isTemporal(final String _symbol) {
        return TEMP_OPER.contains(_symbol);
    }
    
    public static boolean isFirstOrder(final String _symbol) {
        return FIRST_OPER.contains(_symbol);
    }
    
    public static void init() {
        TEMP_OPER.add("P");
        TEMP_OPER.add("N");
        TEMP_OPER.add("U");
        TEMP_OPER.add("S");
        TEMP_OPER.add("A");
        
        FIRST_OPER.add("!");
        FIRST_OPER.add("&");
        FIRST_OPER.add("E");
        FIRST_OPER.add("V");
        
        FIRST_OPER.add("|");
        FIRST_OPER.add("->");
        
        /*
        OPER.put("!", "not");
        OPER.put("&", "and");
        
        OPER.put("E", "exist");
        OPER.put("V", "all");
        
        OPER.put("|", "or");
        OPER.put("->", "imply");
        
        
        OPER.put("P", "prenext");
        OPER.put("N", "next");
        OPER.put("S", "succeed");
        OPER.put("U", "until");
        OPER.put("A", "always");
        */
        logger.info("\nOperator initialization ..........................");
    }
}

/*
 * 
 */
class Interval {
    public int start;
    public int end;
    
    /*
     *@ requires _start >= 0  && _start <= _end
     */
    Interval (int _start, int _end) {
        start = _start;
        end = _end;
    }
    
    Interval (int _start) {
        start = _start;
        end = -1;
    }
    
    Interval () {
        start = 0;
        end = -1;
    }
    
    public boolean inRange(int val) {
        return ((val > start) & ((val < end) | (end == -1)));
    }
    
    public boolean isBounded() {
        return (end == -1);
    }
    
    public String toString() {
        return " [" + start + "," + ((end == -1)?"inf.":end) + ") ";
    }
}

class Signature {
    public Set constant;
    public Set predicate;
    
    public Signature() {
        constant = new HashSet();
        predicate = new HashSet();
        initializeConstant();
        initializePredicate();
    }
    
    private void initializeConstant() {
        
    }
    
    private void initializePredicate() {
        
    }
}