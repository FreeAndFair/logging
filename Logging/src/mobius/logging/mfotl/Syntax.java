package mobius.logging.mfotl;

//TODO add specs and docs

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

/**
 * Define Variables, and if it is free or not
 */
class Variable {
    // Attributes
    private final String my_name;       // variable name
    private boolean my_is_free;         // variable is free or not
    private int my_value;               // variable value after assignment or evaluation
    
    // Constructor
    
    //@ assignable my_name;
    //@ ensures my_name == a_name;
    //@ ensures my_is_free == true;
    public Variable(final String a_name) {
        my_name = a_name;
        my_is_free = true;
    }
    
    // Public Methods
    
    //@ pure
    public String getName() {
        return my_name;
    }
    
    //@ assignable my_is_free;
    //@ ensures my_is_free == a_is_free;
    public void setFree(final boolean a_is_free) {
        my_is_free = a_is_free;
    }
    
    //@ pure
    public boolean isFree() {
        return my_is_free;
    }
    
    //@ assignable my_value;
    //@ ensures my_value == a_value;
    public void setValue(final int a_value) {
        my_value = a_value;
    }
    
    //@ pure
    public int getValue() {
        return my_value;
    }

    //@ assignable my_value;
    public int evaluate(final Structure a_structure) {
        my_value = a_structure.evaluateVar(my_name);
        return my_value;
    }
}

/**
 * <code>Predicator</code> in logical expression
 * 
 */
class Predicate {
    // Attributes
    private final int my_arity;
    private final String my_symbol;
    private final Variable[] my_var;
    
    // Constructors
    
    public Predicate(final Predicate a_predicate, final int a_inc, final String a_name) {
        my_symbol = a_name;
        my_arity = a_predicate.my_arity + a_inc;
        
        
        my_var = new Variable[my_arity];
        System.arraycopy(my_var, 0, a_predicate.my_var, 0, a_predicate.my_arity);
        for (int i = 0; i < a_inc; i++) {
            // TODO ensure no conflict, and maintain order of variable
            my_var[i+a_predicate.my_arity] = new Variable("add_v" + i);
        }
    }
    
    /*
     * @ ensures _var.length == _arity;
     * @ ensures _arity > 0;
     */
    public Predicate(final String a_name, final int a_arity, final String[] _var) {
        my_symbol = a_name;
        my_arity = a_arity;
        
        my_var = new Variable[my_arity];
        for (int i = 0; i < my_arity; i++) {
            my_var[i] = new Variable(_var[i]);
        }
    }
    
    // Public Methods
    
    public boolean evaluate(final /*@ non_null @*/ Structure a_structure) {
        int[] temp_val = new int[my_arity];
        for (int i = 0; i < my_arity; i++) {
            temp_val[i] = my_var[i].evaluate(a_structure);
        }
        
        return a_structure.evaluateRelation(my_symbol, temp_val);
    }
    
    /**
     * <p>
     * return a <code>String</code> that represents the formula
     * </p>
     */
    public String toString() {
        String temp_result = my_symbol;
        
        temp_result = temp_result.concat(" (" + my_var[0].getName());
        for (int i = 1; i < my_arity; i++) {
            temp_result = temp_result.concat(", " + my_var[i].getName());
        }
        temp_result = temp_result.concat(")");
        return temp_result;
    }
    
    //@ pure
    public String getSymbol() {
        return my_symbol;
    }
    
    //@ pure
    public int getArity() {
        return my_arity;
    }
}

class QuantifierOperator extends Operator {
    // Attribute
    private Set<String> my_bound_variable;

    // Constructor
    public QuantifierOperator(final /*@ non_null @*/ String a_name) {
        super(a_name);
        my_bound_variable = new HashSet();
    }
    
    // Public Methods
    //@ assignable my_bound_variable;
    public void addVariable(final /*@ non_null @*/ Set<String> a_set) {
        my_bound_variable = Collections.unmodifiableSet(a_set);
    }
    
    //@ pure
    public boolean isBoundVariable(final /*@ non_null @*/ String a_name) {
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
    
    //@ assignable my_interval
    public void setInterval(final int a_start, final int a_end) {
        my_interval.setStart(a_start);
        my_interval.setEnd(a_end);
    }
    
    //@ pure
    public int getStart() {
        return my_interval.getStart();
    }
    
    //@ pure
    public int getEnd() {
        return my_interval.getEnd();
    }
    
    //@ pure
    public boolean inRange(final int a_testVal) {
        return my_interval.inRange(a_testVal);
    }
    
    //@ pure
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
    public Set<Predicate> my_predicate;
    
    public Signature() {
        my_constant = new HashSet();
        my_predicate = new HashSet();
        initializeConstant();
        initializePredicate();
    }
    
    /*
     * 
     */
    private void initializeConstant() {
        
    }
    
    /*
     * 
     */
    private void initializePredicate() {
        
    }
    
    public void addPredicate(final Predicate a_predicator) {
        my_predicate.add(a_predicator);
    }
    
    public void addConstant() {
        
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
    
    public static boolean isTemporal(final String a_symbol) {
        return TEMP_OPER.contains(a_symbol);
    }

    //@ pure
    public static boolean isFirstOrder(final String a_symbol) {
        return FIRST_OPER.contains(a_symbol);
    }
    
    //@ pure
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