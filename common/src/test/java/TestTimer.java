import io.netty.util.HashedWheelTimer;
import io.netty.util.Timeout;
import io.netty.util.Timer;
import io.netty.util.TimerTask;

import java.util.Set;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicIntegerFieldUpdater;

import static io.netty.util.HashedWheelTimer.*;

/**
 * Created by @author circle.cheung on 2022/3/18 19:41.
 * <p>
 * Description:
 */
public class TestTimer implements Timer {

    private static final AtomicIntegerFieldUpdater<TestTimer> WORKER_STATE_UPDATER =
            AtomicIntegerFieldUpdater.newUpdater(TestTimer.class, "workerState");

    private volatile int workerState; // 0 - init, 1 - started, 2 - shut down
    public static void main(String[] args) {
        TestTimer testTimer = new TestTimer();
        System.out.println(WORKER_STATE_UPDATER.get(testTimer));
        switch (WORKER_STATE_UPDATER.get(testTimer)) { // 针对worker的状态进行switch
            case WORKER_STATE_INIT: // 判断当前时间轮的状态，如果是初始化，则启动worker线程，启动整个时间轮；
                if (WORKER_STATE_UPDATER.compareAndSet(testTimer, WORKER_STATE_INIT, WORKER_STATE_STARTED)) { // 这里是一个Lock Free的设计。因为可能有多个线程调用启动方法，这里使用AtomicIntegerFieldUpdater原子的更新时间轮的状态
                    System.out.println(WORKER_STATE_UPDATER.get(testTimer));
                }
                break;
            case WORKER_STATE_STARTED: // 如果已经启动则略过
                break;
            case WORKER_STATE_SHUTDOWN: // 如果是已经停止，则报错
                throw new IllegalStateException("cannot be started once stopped");
            default:
                throw new Error("Invalid WorkerState");
        }
        System.out.println(WORKER_STATE_UPDATER.get(testTimer));
    }

    @Override
    public Timeout newTimeout(TimerTask task, long delay, TimeUnit unit) {
        return null;
    }

    @Override
    public Set<Timeout> stop() {
        return null;
    }
}
