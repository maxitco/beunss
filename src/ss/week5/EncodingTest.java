package ss.week5;

import org.apache.commons.codec.DecoderException;
import org.apache.commons.codec.binary.Base64;
import org.apache.commons.codec.binary.Hex;

/**
 * A simple class that experiments with the Hex encoding
 * of the Apache Commons Codec library.
 *
 */
public class EncodingTest {
    public static void main(String[] args) throws DecoderException {
        
        /*
         * Hex
         */
        String input = "Hello Big World";
                
        System.out.println(Hex.encodeHexString(input.getBytes()));
        
        String hexString = "4d6f64756c652032";
        
        //String output2 = new String(Hex.decodeHex(input2.toCharArray()));
        //System.out.println(output2);
        System.out.println(new String(Hex.decodeHex(hexString.toCharArray())));
        
        /*
         * Base 64 
         */
        
        String input3 = "Hello World";
        System.out.println(Base64.encodeBase64(input3.getBytes()));
        
        String hexString2 = "010203040506";
        System.out.println(Base64.encodeBase64(Hex.decodeHex(hexString.toCharArray())));
        
        String base64String = "U29mdHdhcmUgU3lzdGVtcw==";
        System.out.println(new String(Base64.decodeBase64(base64String)));
        
        String again = "Software Systems";
        System.out.println(new String(Base64.encodeBase64(again.getBytes())));
        
        //ugly
        String input4 = "";
        for(int i = 1; i <= 4; i++) {
            input4 = input4.concat("a");
            System.out.println(new String(Base64.encodeBase64(input3.getBytes())));    
        }  
    }
}
