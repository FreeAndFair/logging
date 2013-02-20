package mobius.logging.mfotl;

//TODO add specs and docs

import java.util.HashSet;
import java.util.Set;

/**
 * Define Variables, and if it is free or not
 */
class Variable {
    private final String my_name;       // variable name
    private boolean is_free;            // variable is free or not
    private int my_value;               // variable value after assignment or evaluation
    
    public Variable(final String _name) {
        my_name = _name;
        is_free = true;
    }
    
    public String getName() {
        return my_name;
    }
    
    public void setFree(final boolean _is_free) {
        is_free = _is_free;
    }
    
    public boolean isFree() {
        return is_free;
    }
    
    public void setValue(final int _value) {
        my_value = _value;
    }
    
    public int getValue() {
        return my_value;
    }

    //@ assignable my_value
    public int evaluate(final Structure _structure) {
        my_value = _structure.evaluateVar(my_name);
        return my_value;
    }
}

/**
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
        String _result = symbol;
        
        _result = _result.concat(" (" + var[0].getName());
        for (int i = 1; i < arity; i++) {
            _result = _result.concat(", " + var[i].getName());
        }
        _result = _result.concat(")");
        return _result;
    }
    
    public String getSymbol() {
        return symbol;
    }
    
    public int getArity() {
        return arity;
    }
}

class QuantifierOperator extends Operator {
    private final Set my_bound_variable;
    
    public QuantifierOperator(final String a_name) {
        super(a_name);
        my_bound_variable = new HashSet();
    }
    
    public boolean isBoundVariable(final String a_name) {
        return my_bound_variable.contains(a_name);
    }
}

class TemporalOperator extends Operator {
    //public static final Hashtable<String, String> op = new Hashtable<String, String>();

    private final Interval my_interval;
    
    //@ assignable interval
    public TemporalOperator(final /*@ non_null @*/ String _symbol, final int _start, final int _end) {
        super(_symbol);
        my_interval = new Interval(_start, _end);
    }
    
    //@ assignable interval 
    public TemporalOperator(final /*@ non_null @*/ String _symbol, final int _start) {
        super(_symbol);
        my_interval = new Interval(_start);
    }
    
    //@ assignable interval
    public TemporalOperator(final /*@ non_null @*/ String _symbol) {
        super(_symbol);
        my_interval = new Interval();
    }
    
    //@ assignable interval.starty
    public void setStart(final int a_start) {
        my_interval.setStart(a_start);
    }
    
    //@ assignable interval.end
    public void setEnd(final int a_end) {
        my_interval.setEnd(a_end);
    }
    
    public void setInterval(final int a_start, final int a_end) {
        my_interval.setStart(a_start);
        my_interval.setEnd(a_end);
    }
    
    public int getStart() {
        return my_interval.getStart();
    }
    
    public int getEnd() {
        return my_interval.getEnd();
    }
    
    public boolean inRange(final int a_testVal) {
        return my_interval.inRange(a_testVal);
    }
}

class FirstOrder_Operator extends Operator {
    //public static final Hashtable<String, String> op = new Hashtable<String, String>();
    
    FirstOrder_Operator() {
        super();
    }
}

class Operator {
    private static final Set TEMP_OPER = new HashSet();
    private static final Set FIRST_OPER = new HashSet();

    public String my_symbol;
    private static Logger my_logger = new Logger();
    
    public Operator() {
        init();
    }
    
    public Operator(final /*@non-null */ String _symbol) {
        my_symbol = _symbol;
    }
    
    public static boolean isTemporal(final String _symbol) {
        return TEMP_OPER.contains(_symbol);
    }
    
    public static boolean isFirstOrder(final String _symbol) {
        return FIRST_OPER.contains(_symbol);
    }
    
    public static boolean isOperator(final String _symbol) {
        return (isTemporal(_symbol) || isFirstOrder(_symbol));
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
        
        my_logger.info("\nOperator initialization ..........................");
    }
}

/**
 * 
 */
class Interval {
    private int my_start;
    private int my_end;
    
    /*
     *@ requires _start >= 0  && _start <= _end
     */
    public Interval (final int _start, final int _end) {
        my_start = _start;
        my_end = _end;
    }
    
    public Interval (final int _start) {
        my_start = _start;
        my_end = -1;
    }
    
    public Interval () {
        my_start = 0;
        my_end = -1;
    }
    
    public void setStart(final int a_start) {
        my_start = a_start;
    }
    
    public int getStart() {
        return my_start;
    }
    
    public void setEnd(final int a_end) {
        my_end = a_end;
    }
    
    public int getEnd() {
        return my_end;
    }
    
    public boolean inRange(final int a_value) {
        return ((a_value > my_start) & ((a_value < my_end) | (my_end == -1)));
    }
    
    public boolean isBounded() {
        return (my_end == -1);
    }
    
    public String toString() {
        return " [" + my_start + "," + ((my_end == -1)?"inf.":my_end) + ") ";
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