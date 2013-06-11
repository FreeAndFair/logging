package demtech.mfotl;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

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
    
    public /*@ pure @*/ boolean isBoundVariable(final /*@ non_null @*/ String a_name) {
        return my_bound_variable.contains(a_name);
    }
    
    public /*@ pure @*/ Set<String> getBoundVariables() {
        return this.my_bound_variable;
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
    // Attribute
    private final Interval my_interval;
    
    // Constructors
    //@ assignable my_interval
    public TemporalOperator(final String _symbol, final int _start, final int _end) {
        super(_symbol);
        my_interval = new Interval(_start, _end);
    }
    
    //@ assignable my_interval
    public TemporalOperator(final String _symbol, final int _start) {
        super(_symbol);
        my_interval = new Interval(_start);
    }
    
    //@ assignable my_interval
    public TemporalOperator(final String _symbol) {
        super(_symbol);
        my_interval = new Interval();
    }
    
    // Public Methods
    //@ pure
    public void setStart(final int a_start) {
        my_interval.setStart(a_start);
    }
    
    //@ pure
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
    public boolean inRange(final int a_test_val) {
        return my_interval.inRange(a_test_val);
    }
    
    //@ pure
    public boolean gtLower(final int a_test_val) {
        return (a_test_val>my_interval.getStart());
    }
    
    //@ pure
    public boolean ltUpper(final int a_test_val) {
        return (a_test_val < my_interval.getEnd() || my_interval.getEnd() == -1);
    }
    
    //@ pure
    public String toString() {
        return (my_name + my_interval.toString());
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
    // Attributes
    protected final String my_name;
    
    // Constructor
    //@ assignable my_name
    public Operator(final /*@non-null */ String a_name) {
        my_name = a_name;
    }
    
    //@ pure
    public String getName() {
        return this.my_name;
    }
}

class Interval {
    private int my_start;
    private int my_end;
    
    //@ requires _start >= 0  && _start <= _end
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
        return ((a_value >= my_start) && ((a_value < my_end) || (my_end == -1)));
    }
    
    public boolean isBounded() {
        return (my_end == -1);
    }
    
    public String toString() {
        return "[" + my_start + "," + ((my_end == -1)?"inf.":my_end) + ") ";
    }
}

class ReservedSymbol {
    private static final Set<String> TEMP_OPER;
    private static final Set<String> FIRST_OPER;
    private static final Set<String> QUANTIFIER_OPER;
    private static final Set<String> SYMBOL;
    
    private ReservedSymbol() {}
    
    private static void fillTemporalSet(final Set<String> a_set) {
        a_set.add("P");
        a_set.add("N");
        a_set.add("U");
        a_set.add("S");
        a_set.add("A");
    }
    
    private static void fillFirstorderSet(final Set<String> a_set) {
        a_set.add("!");
        a_set.add("&");
        a_set.add("|");
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
    
    //@ pure
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
    
    //@ pure
    public static boolean isSymbol(final String a_symbol) {
        return SYMBOL.contains(a_symbol);
    }
    
    //@ pure
    public static boolean isOperator(final String a_symbol) {
        return (isTemporal(a_symbol) || isFirstOrder(a_symbol) || isQuantifier(a_symbol));
    }
    
    //@ pure
    public static boolean isReserved(final String a_symbol) {
        return (isOperator(a_symbol) || isSymbol(a_symbol));
    }
}