package mobius.logging.mfotl;

//TODO add specs and docs

import java.util.Hashtable;

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
}

/*
 * Predicate in logical expression
 */
class Predicator {
    private final int arity;
    private final String symbol;
    private Variable[] var;
    
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
    
    /* 
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
    
    public boolean valueAssignment() {
        return false;
    }
    
    public String getSymbol() {
        return symbol;
    }
    
    public int getArity() {
        return arity;
    }
}

class TemporalOperator extends Operator {
    //public static final Hashtable<String, String> op = new Hashtable<String, String>();

    final Interval interval;
    
    public TemporalOperator(String _symbol, int _start, int _end) {
        super(_symbol);
        interval = new Interval(_start, _end);
    }
    
    public TemporalOperator(String _symbol, int _start) {
        super(_symbol);
        interval = new Interval(_start);
    }
    
    public TemporalOperator(String _symbol) {
        super(_symbol);
        interval = new Interval();
    }
    
    public void setStart(int _start) {
        interval.start = _start;
    }
    
    public void setEnd(int _end) {
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
    public static final Hashtable<String, String> OPER = new Hashtable<String, String>();

    public String symbol;
    private static Logger logger = new Logger();
    
    Operator() {
        init();
    }
    
    Operator(String _symbol) {
        symbol = _symbol;
    }
    
    public static void init() {
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
        
        logger.info("\nOperator initialization ..........................");
    }
}

/*
class Op {
    String name;
    String symbol;
    
    Op(String _symbol, String _name) {
        name = _name;
        symbol = _symbol;
    }
}
*/

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