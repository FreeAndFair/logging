package mobius.logging.mfotl;

//TODO add specs and docs

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

/**
 * Define Variables, and if it is free or not
 */
class Variable {
    private final String my_name;       // variable name
    private boolean my_is_free;            // variable is free or not
    private int my_value;               // variable value after assignment or evaluation
    
    public Variable(final String _name) {
        my_name = _name;
        my_is_free = true;
    }
    
    public String getName() {
        return my_name;
    }
    
    public void setFree(final boolean _is_free) {
        my_is_free = _is_free;
    }
    
    public boolean isFree() {
        return my_is_free;
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
    private final int my_arity;
    private final String my_symbol;
    private final Variable[] my_var;
    
    /*
     * @ ensures _var.length == _arity;
     * @ ensures _arity > 0;
     */
    public Predicator(final String _name, final int _arity, final String[] _var) {
        my_symbol = _name;
        my_arity = _arity;
        
        my_var = new Variable[my_arity];
        for (int i = 0; i < my_arity; i++) {
            my_var[i] = new Variable(_var[i]);
        }
    }
    
    public boolean evaluate(final Structure _structure) {
        int[] temp_val = new int[my_arity];
        for (int i = 0; i < my_arity; i++) {
            temp_val[i] = my_var[i].evaluate(_structure);
        }
        
        return _structure.evaluateRelation(my_symbol, temp_val);
    }
    
    /**
     * <p>
     * return a <code>String</code> that represents the formula
     * </p>
     */
    public String toString() {
        String _result = my_symbol;
        
        _result = _result.concat(" (" + my_var[0].getName());
        for (int i = 1; i < my_arity; i++) {
            _result = _result.concat(", " + my_var[i].getName());
        }
        _result = _result.concat(")");
        return _result;
    }
    
    public String getSymbol() {
        return my_symbol;
    }
    
    public int getArity() {
        return my_arity;
    }
}

class QuantifierOperator extends Operator {
    private Set<String> my_bound_variable;
    
    public QuantifierOperator(final String a_name) {
        super(a_name);
        my_bound_variable = new HashSet();
    }
    
    public void addVariable(final Set<String> a_set) {
        my_bound_variable = Collections.unmodifiableSet(a_set);
    }
    
    public boolean isBoundVariable(final String a_name) {
        return my_bound_variable.contains(a_name);
    }
    
    public String toString() {
        String temp_str = "";
        
        for (String i : my_bound_variable) {
            temp_str = temp_str.concat(i).concat(" ");
        }
        
        return (my_name + "(" + temp_str + ")");
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
    
    public String toString() {
        String temp_str = my_name;
        temp_str = temp_str.concat(my_interval.toString());
        return temp_str;
    }
}

class FirstorderOperator extends Operator {
    public FirstorderOperator(final String a_name) {
        super(a_name);
    }
    
    public String toString() {
        return my_name;
    }
}

class Operator {
    public String my_name;
    
    public Operator(final /*@non-null */ String _symbol) {
        my_name = _symbol;
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
        return "[" + my_start + "," + ((my_end == -1)?"inf.":my_end) + ") ";
    }
}

class Signature {
    public Set my_constant;
    public Set my_predicate;
    
    public Signature() {
        my_constant = new HashSet();
        my_predicate = new HashSet();
        initializeConstant();
        initializePredicate();
    }
    
    private void initializeConstant() {
        
    }
    
    private void initializePredicate() {
        
    }
}

class ReservedSymbol {
    private static final Set<String> TEMP_OPER;
    private static final Set<String> FIRST_OPER;
    private static final Set<String> QUANTIFIER_OPER;
    private static final Set<String> SYMBOL;
    
    private ReservedSymbol() {}
    
    private static void fillTemporalSet(final Set<String> a_set) {
        a_set.add("P"); // previous next
        a_set.add("N");
        a_set.add("U");
        a_set.add("S");
        a_set.add("A");
    }
    
    private static void fillFirstorderSet(final Set<String> a_set) {
        a_set.add("!");
        a_set.add("&");
        a_set.add("|");
        a_set.add("->");
    }
    
    private static void fillQuantifierSet(final Set<String> a_set) {
        a_set.add("E");
        a_set.add("V");
    }
    
    private static void fillSymbolSet(final Set<String> a_set) {
        a_set.add("(");
        a_set.add(")");
        a_set.add("[");
        a_set.add(",");
        a_set.add("=");
        a_set.add("<");
        a_set.add(" ");
    }
    
    static {
        final Set<String> temp_set0 = new HashSet<String>();
        fillTemporalSet(temp_set0);
        TEMP_OPER = Collections.unmodifiableSet(temp_set0);
        
        final Set<String> temp_set1 = new HashSet<String>();
        fillFirstorderSet(temp_set1);
        FIRST_OPER = Collections.unmodifiableSet(temp_set1);
        
        final Set<String> temp_set2 = new HashSet<String>();
        fillQuantifierSet(temp_set2);
        QUANTIFIER_OPER = Collections.unmodifiableSet(temp_set2);
        
        final Set<String> temp_set3 = new HashSet<String>();
        fillSymbolSet(temp_set3);
        SYMBOL = Collections.unmodifiableSet(temp_set3);
    }
    
    public static boolean isTemporal(final String _symbol) {
        return TEMP_OPER.contains(_symbol);
    }
    
    public static boolean isFirstOrder(final String _symbol) {
        return FIRST_OPER.contains(_symbol);
    }
    
    public static boolean isQuantifier(final String a_symbol) {
        return QUANTIFIER_OPER.contains(a_symbol);
    }
    
    public static boolean isSymbol(final String a_symbol) {
        return SYMBOL.contains(a_symbol);
    }
    
    public static boolean isOperator(final String _symbol) {
        return (isTemporal(_symbol) || isFirstOrder(_symbol) || isQuantifier(_symbol));
    }
    
    public static boolean isReserved(final String _symbol) {
        return (isOperator(_symbol) || isSymbol(_symbol));
    }
}