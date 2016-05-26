import { connect } from 'react-redux'
import { validateFunction } from '../actions'
import FunctionInput from '../components/FunctionInput'

const mapStateToProps = (state) => (
  state.fn    
)

const mapDispatchToProps = (dispatch) => (
  {
    onValidateClick: (fn) => dispatch(validateFunction(fn))
  }
)

const RFunctionInput = connect(
  mapStateToProps,
  mapDispatchToProps
)(FunctionInput)

export default RFunctionInput

