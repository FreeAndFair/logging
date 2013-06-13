package demtech.mfotl.unittest;

import static org.junit.Assert.assertEquals;

import java.util.Arrays;
import java.util.Collection;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import demtech.mfotl.Predicate;


@RunWith(value = Parameterized.class)
public class Test_Predicate {
    private final Predicate a_pred;
    private final String a_str_result;
    private final int a_int_result;
    
    public Test_Predicate(final String a_name, final int a_arity) {
        a_pred = new Predicate(a_name, a_arity);
        a_str_result = a_name;
        a_int_result = a_arity;
    }
    
    @Parameters
    public static Collection<Object[]> data() {
        final Object[][] data = new Object[][] {{"approve", 2}, {"out", 1}, {"in", 1}, {"True", 0}, {"False", 0}};
        return Arrays.asList(data);
    }

    @Test
    public void test() {
        System.out.println(a_pred.toString());
        assertEquals(a_str_result, a_pred.getName());
        assertEquals(a_int_result, a_pred.getArity());
    }
}