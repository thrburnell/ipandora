import { connect } from 'react-redux'
import ClearButton from '../components/ClearButton'
import { clearProof } from '../actions'

const mapStateToProps = () => ({})

const mapDispatchToProps = (dispatch) => (
  {
    onButtonClick: () => dispatch(clearProof())
  }
)

const RClearButton = connect(
  mapStateToProps,
  mapDispatchToProps
)(ClearButton)

export default RClearButton

