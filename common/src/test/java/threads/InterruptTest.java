package threads;

/**
 * Created by @author circle.cheung on 2022/3/18 20:35.
 * <p>
 * Description:
 */
public class InterruptTest {

    public static void main(String[] args) {
        Thread t = new Thread(new InterruptThread());
        t.start();
        boolean interrupted = false;// 终端worker线程
        if (t.isAlive()) {
            System.out.println("--t.isAlive()--" + t.isAlive());
            t.interrupt();
            System.out.println("--t.isAlive() 2--" + t.isAlive());
            System.out.println("--t.isInterrupted()1--" + t.isInterrupted());

            try {
                System.out.println("--t.isInterrupted()2--" + t.isInterrupted());
                t.join(100);
            } catch (InterruptedException ignored) {
                interrupted = true;
                System.out.println("--interrupted--" + interrupted);
            }
        }
    }

    static class InterruptThread implements Runnable {
        @Override
        public void run() {
            try {
                Thread.sleep(2000);
            } catch (InterruptedException e) {
                System.out.println("线程处于阻塞状态时，中断线程，就会抛出异常。");
                e.printStackTrace();
            }

        }
    }
}
