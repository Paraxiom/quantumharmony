#![cfg_attr(not(feature = "std"), no_std)]

pub use pallet::*;

pub mod runtime_api;

#[frame_support::pallet]
pub mod pallet {
    use frame_support::pallet_prelude::*;
    use frame_system::pallet_prelude::*;
    use sp_std::vec::Vec;

    #[pallet::pallet]
    pub struct Pallet<T>(_);

    #[pallet::config]
    pub trait Config: frame_system::Config {
        type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;
        
        /// Maximum message length
        #[pallet::constant]
        type MaxMessageLength: Get<u32>;
        
        /// Maximum messages stored
        #[pallet::constant]
        type MaxMessages: Get<u32>;
    }

    /// A message in the forum
    #[derive(Clone, Encode, Decode, TypeInfo, MaxEncodedLen)]
    #[scale_info(skip_type_params(T))]
    pub struct Message<T: Config> {
        pub sender: T::AccountId,
        pub block: BlockNumberFor<T>,
        pub content: BoundedVec<u8, T::MaxMessageLength>,
    }

    /// All messages stored on-chain
    #[pallet::storage]
    #[pallet::getter(fn messages)]
    pub type Messages<T: Config> = StorageValue<
        _,
        BoundedVec<Message<T>, T::MaxMessages>,
        ValueQuery,
    >;

    /// Message count
    #[pallet::storage]
    #[pallet::getter(fn message_count)]
    pub type MessageCount<T> = StorageValue<_, u32, ValueQuery>;

    #[pallet::event]
    #[pallet::generate_deposit(pub(super) fn deposit_event)]
    pub enum Event<T: Config> {
        /// Message posted [sender, message_id, content_preview]
        MessagePosted {
            sender: T::AccountId,
            message_id: u32,
            block: BlockNumberFor<T>,
        },
    }

    #[pallet::error]
    pub enum Error<T> {
        /// Message too long
        MessageTooLong,
        /// Forum is full
        ForumFull,
        /// Empty message
        EmptyMessage,
    }

    #[pallet::call]
    impl<T: Config> Pallet<T> {
        /// Post a message to the forum
        #[pallet::call_index(0)]
        #[pallet::weight(10_000)]
        pub fn post_message(
            origin: OriginFor<T>,
            content: Vec<u8>,
        ) -> DispatchResult {
            let sender = ensure_signed(origin)?;
            
            ensure!(!content.is_empty(), Error::<T>::EmptyMessage);
            
            let bounded_content: BoundedVec<u8, T::MaxMessageLength> = 
                content.try_into().map_err(|_| Error::<T>::MessageTooLong)?;
            
            let block = <frame_system::Pallet<T>>::block_number();
            let message_id = Self::message_count();
            
            let message = Message {
                sender: sender.clone(),
                block,
                content: bounded_content,
            };
            
            Messages::<T>::try_mutate(|messages| {
                if messages.is_full() {
                    // Rolling window: drop oldest message to make room
                    messages.remove(0);
                }
                messages.try_push(message).map_err(|_| Error::<T>::ForumFull)
            })?;
            
            MessageCount::<T>::put(message_id.saturating_add(1));
            
            Self::deposit_event(Event::MessagePosted {
                sender,
                message_id,
                block,
            });
            
            Ok(())
        }
    }
}
