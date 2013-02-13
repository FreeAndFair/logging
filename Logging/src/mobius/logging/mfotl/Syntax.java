package mobius.logging.mfotl;

import java.util.Hashtable;

/*
 * Define Variables, and if it is free or not
 */
class Variable {
    String name;
    boolean is_free;
    
    Variable(String _name) {
        name = _name;
        is_free = true;
    }
    
    void setFree(boolean _is_free) {
        is_free = _is_free;
    }
}

/*
 * Predicate in logical expression
 */
class Predicate {
    int arity;
    String name;
    Variable[] var;
    
    /*
     * @ ensures _var.length == _arity;
     * @ ensures _arity > 0;
     */
    Predicate(String _name, int _arity, String[] _var) {
        name = _name;
        arity = _arity;
        
        var = new Variable[10];
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
        String _result;
        _result = name + " (" + var[0].name;
        for (int i = 1; i < arity; i++) {
            _result += (", " + var[i].name);
        }
        _result += ")";
        return _result;
    }
    
    public boolean valueAssignment() {
        return false;
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
    
    Operator() {
        init();
    }
    
    Operator(String _symbol) {
        symbol = _symbol;
    }
    
    static void init() {
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
        
        System.out.println("\nOperator initialization ..........................");
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
        return " [" + start + "," + ((end == -1)?("inf."):(end)) + ") ";
    }
}