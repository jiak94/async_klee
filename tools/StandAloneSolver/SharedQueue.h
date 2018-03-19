//
// Created by jiakuan on 3/18/18.
//
#ifndef KLEE_SHAREDQUEUE_H
#define KLEE_SHAREDQUEUE_H
#include <mutex>
#include <condition_variable>
#include <queue>
#include <string>

class SharedQueue {
public:
    SharedQueue();

    ~SharedQueue();

    std::string &front();

    void pop_front();

    void push_back(const std::string &item);

    void push_back(std::string &&item);

    int size();

    bool empty();

private:
    std::deque<std::string> queue_;
    std::mutex mutex_;
    std::condition_variable cond_;
};
SharedQueue::SharedQueue() {}


SharedQueue::~SharedQueue() {}


std::string &SharedQueue::front() {
    std::unique_lock<std::mutex> mlock(mutex_);
    while (queue_.empty()) {
        cond_.wait(mlock);
    }
    return queue_.front();
}

void SharedQueue::pop_front() {
    std::unique_lock<std::mutex> mlock(mutex_);
    while (queue_.empty()) {
        cond_.wait(mlock);
    }
    queue_.pop_front();
}

void SharedQueue::push_back(const std::string &item) {
    std::unique_lock<std::mutex> mlock(mutex_);
    queue_.push_back(item);
    mlock.unlock();     // unlock before notificiation to minimize mutex con
    cond_.notify_one(); // notify one waiting thread

}

void SharedQueue::push_back(std::string &&item) {
    std::unique_lock<std::mutex> mlock(mutex_);
    queue_.push_back(std::move(item));
    mlock.unlock();     // unlock before notificiation to minimize mutex con
    cond_.notify_one(); // notify one waiting thread

}

int SharedQueue::size() {
    std::unique_lock<std::mutex> mlock(mutex_);
    int size = queue_.size();
    mlock.unlock();
    return size;
}

bool SharedQueue::empty() {
    std::unique_lock<std::mutex> mlock(mutex_);
    bool empty_queue;
    if (queue_.empty()) {
        empty_queue = true;
    }
    else {
        empty_queue = false;
    }
    mlock.unlock();
    return empty_queue;
}

#endif //KLEE_SHAREDQUEUE_H
