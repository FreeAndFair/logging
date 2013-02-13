package mobius.logging.mfotl;

public class MFOTLTest {

    private MFOTLTest() {
        
    }
    
    /**
     * @param args
     * Test
     */
    public static void main(final String[] args) {
        //Formula test = new Formula("A ( ! E x ( in (x) & ! ( E y ( y = y U [ 0 , 6 ) out ( x ) ) )  )  )");
        new Formula("! N[1,5)n(p) ");
        new Formula("N[1,5)n(p) ");
        new Formula("(x=y)&m(a,b)&N[3,5)n(p) ");
        
        new Formula("(( x = y ) &r ( m , n ) & ( z = x ) )");
                
        new Formula("   ( x < y )" );

        new Formula("( r ( a , b ) )");
        new Formula("aar ( a , b , c )");
    }
}
